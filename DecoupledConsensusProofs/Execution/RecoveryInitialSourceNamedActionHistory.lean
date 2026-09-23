module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.RecoveryInitialSourceNamedP6

@[expose] public section

/-!
# earlier-shaped action-history step for the named recovery regime

This module ports earlier's one-round Goldfish step without the stronger
prepared-window input of the retained named core.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem actionHistory_compatible_ancestor
    {A B T : Block V} (hAB : Block.Preceq A B)
    (hBT : Block.compatible B T = true) :
    Block.compatible A T = true := by
  rcases (show Block.Preceq B T ∨ Block.Preceq T B by
    simpa only [Block.compatible, Bool.or_eq_true] using hBT) with hBT | hTB
  · simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inl (Block.preceq_trans hAB hBT)
  · exact Block.compatible_of_preceq_common hAB hTB


/-- The prepared next-duty anchor is compatible with a block protected by
the immediately preceding honest SG batch. In the active-frame branch, the
relative G1 grade has an honest positive supporter from that batch. -/
theorem voterAnchorAt_compatible_of_previousSGHistory_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {s : Slot} {T : Block V}
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hc : 1 ≤ S.hc.round_of (s + 1))
    (hsg : HonestSGEmissionsCompatibleAtRound S rho
      (S.hc.round_of (s + 1) - 1) T)
    (hsgPost : S.E.t_GST ≤ S.a (S.hc.round_of (s + 1) - 1))
    {w : V} (hw : w ∈ rho.honest)
    (hroot : Block.compatible
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w
          (s + 1)).st.core.toHealing.toFG) T = true) :
    Block.compatible (voterAnchorAt S rho w (s + 1)) T = true := by
  let c := S.hc.round_of (s + 1)
  let q := c - 1
  have hqc : q + 1 = c := Nat.sub_add_cancel hc
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
    apply le_trans (le_of_lt ?_) hhor
    rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  rcases voterAnchorAt_cases S rho w (s + 1) with
    hfg | ⟨root, L, hframe, hactive, hanchor⟩
  · rw [hfg]
    exact hroot
  · rw [hanchor]
    have hround : S.hc.round_of (s + 1) = c := rfl
    have hslo : S.hc.opening_slot c ≤ s + 1 := by
      rw [← hround]
      exact Nat.div_mul_le_self (s + 1) S.hc.R
    have hshi : s + 1 < S.hc.opening_slot (c + 1) := by
      rw [← hround]
      apply (Nat.div_lt_iff_lt_mul
        (Nat.zero_lt_of_lt S.hc.R_ge_two)).mp
      exact Nat.lt_succ_self ((s + 1) / S.hc.R)
    have hnext : Protocol.vote_time S.E (s + 1) ≤
        DecoupledConsensusModel.Protocol.opening S.E S.hc (c + 1) := by
      have hvoteNext : Protocol.vote_time S.E (s + 1) <
          Protocol.proposal_time S.E (s + 2) := by
        apply lt_trans ?_ (support_cutoff_lt_proposal_time_succ S.E (s + 1))
        rw [← Proofs.Optimistic.vote_time_add_delta]
        exact Int.lt_add_of_pos_right _ S.E.Δ_pos
      exact hvoteNext.le.trans (by
        simpa only [DecoupledConsensusModel.Protocol.opening] using
          proposal_time_mono S.E (Nat.succ_le_iff.mpr hshi))
    have hframe' : (DecoupledConsensusModel.Protocol.readFrame
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).cache
        (Internal.NamedRecoveryRead.voteDutyRead S rho w
          (s + 1)).st.core.toHealing c).g1 = some (some root) := by
      have hslot :
          (Internal.NamedRecoveryRead.voteDutyRead S rho w
            (s + 1)).st.core.s = s + 1 :=
        Proofs.Optimistic.voteDutyRead_slot S rho w (s + 1)
      simpa only [hslot, hround] using hframe
    obtain ⟨_, hLgrade⟩ := fixedRoot_activeVoterAnchor_g1_data
      S adm (Nat.zero_lt_of_lt hc) hslo hround hnext hvoteHor hw
        hframe' hactive
    rcases (show Block.Preceq
        (Protocol.get_fg_root
          (Internal.NamedRecoveryRead.voteDutyRead S rho w
            (s + 1)).st.core.toHealing.toFG) T ∨
        Block.Preceq T
          (Protocol.get_fg_root
            (Internal.NamedRecoveryRead.voteDutyRead S rho w
              (s + 1)).st.core.toHealing.toFG) by
      simpa only [Block.compatible, Bool.or_eq_true] using hroot) with
      hrootT | hTroot
    · have hdomainVote : DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1 ≤
          Protocol.vote_time S.E (s + 1) := by
        rw [NamedOutageClosure.domain_g1_eq_opening]
        exact (Protocol.proposal_time_mono S.E hslo).trans
          (Protocol.proposal_time_lt_vote_time S.E (s + 1)).le
      have hdomainHor : DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1 ≤
          rho.horizon := hdomainVote.trans hvoteHor
      have hqHor : S.a q ≤ rho.horizon := by
        have hactionDomain : S.a q ≤
            DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1 := by
          apply (le_add_of_nonneg_right S.E.Δ_pos.le).trans
          rw [← hqc]
          apply (NamedOutageClosure.action_delta_le_early
            S S.hc.R_ge_three (Nat.lt_succ_self q)).trans
          simp only [DecoupledConsensusModel.Protocol.early,
            DecoupledConsensusModel.Protocol.Phase.earlyOffset,
            DecoupledConsensusModel.Protocol.domain,
            DecoupledConsensusModel.Protocol.Phase.domainOffset]
          linarith [S.E.Δ_pos]
        exact hactionDomain.trans hdomainHor
      have hvoteFroot : Block.Preceq
          (Internal.NamedRecoveryRead.voteDutyRead S rho w
            (s + 1)).st.core.F
          (Protocol.get_fg_root
            (Internal.NamedRecoveryRead.voteDutyRead S rho w
              (s + 1)).st.core.toHealing.toFG) :=
        StoreFinality.finalized_preceq_fgRoot
          (Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
            S rho (Protocol.vote_time S.E (s + 1)) w)
      have hdomainFvoteF : Block.Preceq
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.F
          (Internal.NamedRecoveryRead.voteDutyRead S rho w
            (s + 1)).st.core.F := by
        simpa only [Internal.NamedRecoveryRead.voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock] using
            (by
              rw [NamedOutageClosure.strict_read_eq_index S rho
                    adm.toNamedScheduleWellFormed.sorted
                    (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1),
                  NamedOutageClosure.strict_read_eq_index S rho
                    adm.toNamedScheduleWellFormed.sorted
                    (Protocol.vote_time S.E (s + 1))]
              exact Proofs.NamedRuntime.stateBefore_F_mono S rho w
                (NamedOutageClosure.strict_lengths_mono rho hdomainVote))
      have hFT : Block.Preceq
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.F T :=
        Block.preceq_trans hdomainFvoteF
          (Block.preceq_trans hvoteFroot hrootT)
      have hinputs : ∀ u ∈ rho.honest, ∃ y ∈
          DecoupledConsensusModel.Protocol.interpretedInputs
            (NamedRun.stateBeforeTime S rho
              (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.toHealing.gradeView
            (NamedRun.stateBeforeTime S rho
              (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.F
            S.hc.η_SG c (DecoupledConsensusModel.Protocol.early S.E S.hc c .g1) u,
          y.round = q := by
        intro u hu
        let b := actionAttestationAt S rho u q
        have hemit : NamedRun.emits S rho u (Object.attest b) (S.a q) :=
          honest_emits_exact_actionAttestationAt S adm hu q hqHor (by assumption)
        obtain ⟨j, hj, _, Hb, hHb, hconfirmed⟩ :=
          Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
        have hcarrierMem : actionSGBlockAt S rho u q ∈
            (NamedRun.stateBeforeTime S rho (S.a q) u).st.core.T :=
          actionSGBlockAt_mem_storeBeforeTime S rho u q
        obtain ⟨D, hDbody, hDerase⟩ :=
          Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
            S rho (S.a q) u hcarrierMem
        obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
          adm.toNamedScheduleWellFormed.sorted (S.a q)
        have hDprefix : D ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
          rw [← hn]
          exact hDbody
        have hHbSource : Hb ∈
            (NamedRun.stateBeforeTime S rho (S.a q) u).st.bodies := by
          have hstate := NamedActionSources.action_read_index S rho
            adm.toNamedScheduleWellFormed j u b.round
              (by simpa only [b, (actionAttestationAt_shape S rho u q).2.1]
                using hj)
          change Hb ∈ (NamedRun.stateBefore S rho j u).st.bodies at hHb
          rw [← (actionAttestationAt_shape S rho u q).2.1, ← hstate]
          exact hHb
        have hHbPrefix : Hb ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
          rw [← hn]
          exact hHbSource
        have hDrun : RunBlock S rho D :=
          Proofs.Bridges.runBlock_of_stateBefore_mem S hu hDprefix
        have hHbrun : RunBlock S rho Hb :=
          Proofs.Bridges.runBlock_of_stateBefore_mem S hu hHbPrefix
        have hrootDH : D.root = Hb.root := by
          rw [← Proofs.NamedWire.erase_root D, hDerase]
          exact Option.some.inj
            ((actionAttestationAt_shape S rho u q).2.2.symm.trans hconfirmed)
        have hDH : D = Hb :=
          adm.toNamedRootCollisionFree.root_injective D Hb hDrun hHbrun
            D Hb (Or.inl (Proofs.NamedAncestry.named_self D))
              (Or.inr (Proofs.NamedAncestry.named_self Hb)) hrootDH
        have hHbErase : Hb.erase = actionSGBlockAt S rho u q := by
          rw [← hDH, hDerase]
        have hcarrierT : Block.compatible Hb.erase T = true := by
          rw [hHbErase]
          exact hsg u hu hemit
        have hk : q ∈ Protocol.latest_window S.hc.η_SG c := by
          rw [← hqc]
          apply NamedOutageClosure.mem_latest_window
          · simpa only [Nat.add_sub_cancel] using
              Nat.sub_le_sub_left S.hc.η_SG_ge_one (q + 1)
          · exact Nat.lt_succ_self q
        have hdeadline : max (S.a b.round) S.E.t_GST + S.E.Δ ≤
            DecoupledConsensusModel.Protocol.early S.E S.hc c .g1 := by
          rw [show b.round = q from (actionAttestationAt_shape S rho u q).2.1,
            max_eq_left hsgPost, ← hqc]
          apply (NamedOutageClosure.action_delta_le_early
            S S.hc.R_ge_three (Nat.lt_succ_self q)).trans
          simp only [DecoupledConsensusModel.Protocol.early,
            DecoupledConsensusModel.Protocol.Phase.earlyOffset]
          linarith [S.E.Δ_pos]
        have horder : DecoupledConsensusModel.Protocol.early S.E S.hc c .g1 ≤
            DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1 := by
          simp only [DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.domain,
            DecoupledConsensusModel.Protocol.Phase.earlyOffset,
            DecoupledConsensusModel.Protocol.Phase.domainOffset]
          linarith [S.E.Δ_pos]
        have hcut : DecoupledConsensusModel.Protocol.early S.E S.hc c .g1 ≤
            rho.horizon := horder.trans hdomainHor
        have hhead : ∃ j : Nat,
            rho.events[j]? = some (.tick u (S.a q)) ∧
            Hb ∈ (NamedActionReads.actionReadFrom S
              (NamedRun.stateBefore S rho j u) b.round).st.bodies ∧
            b.confirmed = some Hb.root := by
          exact ⟨j, hj, hHb, hconfirmed⟩
        rcases (show Block.Preceq Hb.erase T ∨ Block.Preceq T Hb.erase by
          simpa only [Block.compatible, Bool.or_eq_true] using hcarrierT) with
          hHbT | hTHb
        · obtain ⟨y, hy, hyround, -⟩ :=
            interpretedInputs_exact_of_honest_window_vote_after_gst_common_upper
              S adm.toNamedAdmissibleCore .g1 hk hu hw
                ⟨(actionAttestationAt_shape S rho u q).1,
                  (actionAttestationAt_shape S rho u q).2.1, hemit⟩
                hhead hHbT hFT
                (by simpa only [b,
                  (actionAttestationAt_shape S rho u q).2.1] using hsgPost)
                hdeadline horder hcut
          exact ⟨y, hy, hyround⟩
        · obtain ⟨y, hy, hyround, -⟩ :=
            interpretedInputs_exact_of_honest_window_vote_after_gst_common_upper
              S adm.toNamedAdmissibleCore .g1 hk hu hw
                ⟨(actionAttestationAt_shape S rho u q).1,
                  (actionAttestationAt_shape S rho u q).2.1, hemit⟩
                hhead (Block.preceq_self Hb.erase)
                (Block.preceq_trans hFT hTHb)
                (by simpa only [b,
                  (actionAttestationAt_shape S rho u q).2.1] using hsgPost)
                hdeadline horder hcut
          exact ⟨y, hy, hyround⟩
      have hinterpreted : ∀ u ∈ rho.honest,
          (DecoupledConsensusModel.Protocol.interpretedInputs
            (NamedRun.stateBeforeTime S rho
              (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.toHealing.gradeView
            (NamedRun.stateBeforeTime S rho
              (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.F
            S.hc.η_SG c (DecoupledConsensusModel.Protocol.early S.E S.hc c .g1) u).Nonempty := by
        intro u hu
        obtain ⟨y, hy, -⟩ := hinputs u hu
        exact ⟨y, hy⟩
      have hwindow := windowMajorityAt_of_honestWeightMajority_of_interpreted
        S (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow)
          hinterpreted
      have hgrade : DecoupledConsensusModel.Protocol.gradeBool S.E
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.F
          S.hc.η_SG c (DecoupledConsensusModel.Protocol.early S.E S.hc c .g1)
            (DecoupledConsensusModel.Protocol.late S.E S.hc c .g1) L = true := by
        simpa only [PhaseGrades.storeGrade, PhaseGrades.phaseGrade,
          PhaseGrades.readAt] using hLgrade
      obtain ⟨u, hu, _, _, _, _, _, _, _, hpositive⟩ :=
        exists_honest_positive_supporter_of_relativeGrade
          S.E S.hc hwindow hgrade
      simp only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq]
        at hpositive
      obtain ⟨tok, htok, hmax, hcover, _, _⟩ := hpositive
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp htok
      obtain ⟨z, hz, hzRound⟩ := hinputs u hu
      have hyRoundLe : y.round < c := by
        have hyraw := (Finset.mem_filter.mp hy).1
        simp only [DecoupledConsensusModel.Protocol.rawInputs, Finset.mem_filter] at hyraw
        obtain ⟨k, hk, hyk⟩ := Finset.mem_biUnion.mp hyraw.1
        have hyRoundK := GradeDeliveryRun.projected_rounds_storeBeforeTime
          S adm.toNamedScheduleWellFormed w
            (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) k y hyk
        rw [hyRoundK]
        exact (NamedOutageClosure.window_bounds (List.mem_toFinset.mp hk)).2
      have hyRound : y.round = q := by
        have hqLe : q ≤ y.round := by
          rw [← hzRound]
          exact hmax (DecoupledConsensusModel.Protocol.token z)
            (Finset.mem_image_of_mem DecoupledConsensusModel.Protocol.token hz)
        have hyLe : y.round ≤ q := by
          have hlt := hyRoundLe
          rw [← hqc] at hlt
          exact Nat.le_of_lt_succ hlt
        exact Nat.le_antisymm hyLe hqLe
      obtain ⟨key, Head, hyconfirmed, hyfind, _, hLHead⟩ :=
        Proofs.HealingLemmas.exists_head_of_head_covers hcover
      have hyPool : y ∈
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.toHealing.sg_votes q := by
        have hyraw := (Finset.mem_filter.mp hy).1
        simp only [DecoupledConsensusModel.Protocol.rawInputs, Finset.mem_filter] at hyraw
        obtain ⟨k, _, hyk⟩ := Finset.mem_biUnion.mp hyraw.1
        have hyRoundK := GradeDeliveryRun.projected_rounds_storeBeforeTime
          S adm.toNamedScheduleWellFormed w
            (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) k y hyk
        have hkq : k = q := hyRoundK.symm.trans hyRound
        simpa only [hkq] using hyk
      have hySender : y.val_index = u := by
        have hyraw := (Finset.mem_filter.mp hy).1
        simp only [DecoupledConsensusModel.Protocol.rawInputs, Finset.mem_filter] at hyraw
        exact hyraw.2.1
      have hHeadT := rootCompatible_of_emittedSGHistory_at_read
        S adm hw hsg hyPool (hySender ▸ hu)
      have hheadRoot : Head.root = key := Proofs.HealingLemmas.find?_root hyfind
      have hyconfirmed' : y.confirmed = some Head.root := by
        rw [hheadRoot]
        exact hyconfirmed
      have hyfind' : Block.find?
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.T
          Head.root = some Head := by
        rw [hheadRoot]
        exact hyfind
      change rootCompatible
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.T
        T y.confirmed = true at hHeadT
      rw [hyconfirmed'] at hHeadT
      change (match Block.find?
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.T
          Head.root with
        | some H => Block.compatible H T
        | none => true) = true at hHeadT
      rw [hyfind'] at hHeadT
      exact actionHistory_compatible_ancestor hLHead hHeadT
    · have hrootL : Block.Preceq
          (Protocol.get_fg_root
            (Internal.NamedRecoveryRead.voteDutyRead S rho w
              (s + 1)).st.core.toHealing.toFG) L := by
        have hLmem : L ∈ PhaseGrades.filteredTree
            (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)) := by
          unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
          exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).1
        exact Proofs.Records.preceq_get_fg_root_of_mem_filtered hLmem
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr (Block.preceq_trans hTroot hrootL)

#print axioms voterAnchorAt_compatible_of_previousSGHistory_named


/-- A relative phase grade is compatible with a block protected by the
immediately preceding honest SG batch, when the phase finalized root is below
that block. -/
theorem phaseGrade_compatible_of_previousSGHistory_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {c : Round} (hc : 1 ≤ c) {p : DecoupledConsensusModel.Protocol.Phase}
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hdomainHor : DecoupledConsensusModel.Protocol.domain S.E S.hc c p ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) {T B : Block V}
    (hFT : Block.Preceq
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc c p) w).st.core.F T)
    (hsg : HonestSGEmissionsCompatibleAtRound S rho (c - 1) T)
    (hgrade : DecoupledConsensusModel.Protocol.gradeBool S.E
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc c p) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc c p) w).st.core.F
      S.hc.η_SG c (DecoupledConsensusModel.Protocol.early S.E S.hc c p)
        (DecoupledConsensusModel.Protocol.late S.E S.hc c p) B = true) :
    Block.compatible B T = true := by
  let q := c - 1
  have hqc : q + 1 = c := Nat.sub_add_cancel hc
  have hqHor : S.a q ≤ rho.horizon := by
    have hqDomain : S.a q + S.E.Δ ≤
        DecoupledConsensusModel.Protocol.domain S.E S.hc c p := by
      rw [← hqc]
      apply (NamedOutageClosure.action_delta_le_early
        S S.hc.R_ge_three (Nat.lt_succ_self q)).trans
      cases p <;>
        simp only [DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.domain,
          DecoupledConsensusModel.Protocol.Phase.earlyOffset,
          DecoupledConsensusModel.Protocol.Phase.domainOffset] <;>
        linarith [S.E.Δ_pos]
    exact (le_add_of_nonneg_right S.E.Δ_pos.le).trans
      (hqDomain.trans hdomainHor)
  have hinputs : ∀ u ∈ rho.honest, ∃ y ∈
      DecoupledConsensusModel.Protocol.interpretedInputs
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc c p) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc c p) w).st.core.F
        S.hc.η_SG c (DecoupledConsensusModel.Protocol.early S.E S.hc c p) u,
      y.round = q := by
    intro u hu
    let b := actionAttestationAt S rho u q
    have hemit : NamedRun.emits S rho u (Object.attest b) (S.a q) :=
      honest_emits_exact_actionAttestationAt S adm hu q hqHor (by assumption)
    obtain ⟨j, hj, _, Hb, hHb, hconfirmed⟩ :=
      Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
    have hcarrierMem : actionSGBlockAt S rho u q ∈
        (NamedRun.stateBeforeTime S rho (S.a q) u).st.core.T :=
      actionSGBlockAt_mem_storeBeforeTime S rho u q
    obtain ⟨D, hDbody, hDerase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
        S rho (S.a q) u hcarrierMem
    obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
      adm.toNamedScheduleWellFormed.sorted (S.a q)
    have hDprefix : D ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
      rw [← hn]
      exact hDbody
    have hHbSource : Hb ∈
        (NamedRun.stateBeforeTime S rho (S.a q) u).st.bodies := by
      have hstate := NamedActionSources.action_read_index S rho
        adm.toNamedScheduleWellFormed j u b.round
          (by simpa only [b, (actionAttestationAt_shape S rho u q).2.1]
            using hj)
      change Hb ∈ (NamedRun.stateBefore S rho j u).st.bodies at hHb
      rw [← (actionAttestationAt_shape S rho u q).2.1, ← hstate]
      exact hHb
    have hHbPrefix : Hb ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
      rw [← hn]
      exact hHbSource
    have hDrun : RunBlock S rho D :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S hu hDprefix
    have hHbrun : RunBlock S rho Hb :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S hu hHbPrefix
    have hrootDH : D.root = Hb.root := by
      rw [← Proofs.NamedWire.erase_root D, hDerase]
      exact Option.some.inj
        ((actionAttestationAt_shape S rho u q).2.2.symm.trans hconfirmed)
    have hDH : D = Hb :=
      adm.toNamedRootCollisionFree.root_injective D Hb hDrun hHbrun
        D Hb (Or.inl (Proofs.NamedAncestry.named_self D))
          (Or.inr (Proofs.NamedAncestry.named_self Hb)) hrootDH
    have hHbErase : Hb.erase = actionSGBlockAt S rho u q := by
      rw [← hDH, hDerase]
    have hcarrierT : Block.compatible Hb.erase T = true := by
      rw [hHbErase]
      exact hsg u hu hemit
    have hk : q ∈ Protocol.latest_window S.hc.η_SG c := by
      rw [← hqc]
      apply NamedOutageClosure.mem_latest_window
      · simpa only [Nat.add_sub_cancel] using
          Nat.sub_le_sub_left S.hc.η_SG_ge_one (q + 1)
      · exact Nat.lt_succ_self q
    have hdeadline : max (S.a b.round) S.E.t_GST + S.E.Δ ≤
        DecoupledConsensusModel.Protocol.early S.E S.hc c p := by
      rw [show b.round = q from (actionAttestationAt_shape S rho u q).2.1,
        max_eq_left hpost, ← hqc]
      apply (NamedOutageClosure.action_delta_le_early
        S S.hc.R_ge_three (Nat.lt_succ_self q)).trans
      cases p <;> simp only [DecoupledConsensusModel.Protocol.early,
        DecoupledConsensusModel.Protocol.Phase.earlyOffset] <;> linarith [S.E.Δ_pos]
    have horder : DecoupledConsensusModel.Protocol.early S.E S.hc c p ≤
        DecoupledConsensusModel.Protocol.domain S.E S.hc c p := by
      cases p <;> simp only [DecoupledConsensusModel.Protocol.early,
        DecoupledConsensusModel.Protocol.domain, DecoupledConsensusModel.Protocol.Phase.earlyOffset,
        DecoupledConsensusModel.Protocol.Phase.domainOffset] <;> linarith [S.E.Δ_pos]
    have hcut : DecoupledConsensusModel.Protocol.early S.E S.hc c p ≤ rho.horizon :=
      horder.trans hdomainHor
    have hhead : ∃ j : Nat,
        rho.events[j]? = some (.tick u (S.a q)) ∧
        Hb ∈ (NamedActionReads.actionReadFrom S
          (NamedRun.stateBefore S rho j u) b.round).st.bodies ∧
        b.confirmed = some Hb.root := by
      exact ⟨j, hj, hHb, hconfirmed⟩
    rcases (show Block.Preceq Hb.erase T ∨ Block.Preceq T Hb.erase by
      simpa only [Block.compatible, Bool.or_eq_true] using hcarrierT) with
      hHbT | hTHb
    · obtain ⟨y, hy, hyround, -⟩ :=
        interpretedInputs_exact_of_honest_window_vote_after_gst_common_upper
          S adm.toNamedAdmissibleCore p hk hu hw
            ⟨(actionAttestationAt_shape S rho u q).1,
              (actionAttestationAt_shape S rho u q).2.1, hemit⟩
            hhead hHbT hFT
            (by simpa only [b,
              (actionAttestationAt_shape S rho u q).2.1] using hpost)
            hdeadline horder hcut
      exact ⟨y, hy, hyround⟩
    · obtain ⟨y, hy, hyround, -⟩ :=
        interpretedInputs_exact_of_honest_window_vote_after_gst_common_upper
          S adm.toNamedAdmissibleCore p hk hu hw
            ⟨(actionAttestationAt_shape S rho u q).1,
              (actionAttestationAt_shape S rho u q).2.1, hemit⟩
            hhead (Block.preceq_self Hb.erase)
            (Block.preceq_trans hFT hTHb)
            (by simpa only [b,
              (actionAttestationAt_shape S rho u q).2.1] using hpost)
            hdeadline horder hcut
      exact ⟨y, hy, hyround⟩
  have hinterpreted : ∀ u ∈ rho.honest,
      (DecoupledConsensusModel.Protocol.interpretedInputs
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc c p) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc c p) w).st.core.F
        S.hc.η_SG c (DecoupledConsensusModel.Protocol.early S.E S.hc c p) u).Nonempty := by
    intro u hu
    obtain ⟨y, hy, -⟩ := hinputs u hu
    exact ⟨y, hy⟩
  have hwindow := windowMajorityAt_of_honestWeightMajority_of_interpreted
    S (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow)
      hinterpreted
  obtain ⟨u, hu, _, _, _, _, _, _, _, hpositive⟩ :=
    exists_honest_positive_supporter_of_relativeGrade
      S.E S.hc hwindow hgrade
  simp only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq]
    at hpositive
  obtain ⟨tok, htok, hmax, hcover, _, _⟩ := hpositive
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp htok
  obtain ⟨z, hz, hzRound⟩ := hinputs u hu
  have hyRoundLe : y.round < c := by
    have hyraw := (Finset.mem_filter.mp hy).1
    simp only [DecoupledConsensusModel.Protocol.rawInputs, Finset.mem_filter] at hyraw
    obtain ⟨k, hk, hyk⟩ := Finset.mem_biUnion.mp hyraw.1
    have hyRoundK := GradeDeliveryRun.projected_rounds_storeBeforeTime
      S adm.toNamedScheduleWellFormed w
        (DecoupledConsensusModel.Protocol.domain S.E S.hc c p) k y hyk
    rw [hyRoundK]
    exact (NamedOutageClosure.window_bounds (List.mem_toFinset.mp hk)).2
  have hyRound : y.round = q := by
    have hqLe : q ≤ y.round := by
      rw [← hzRound]
      exact hmax (DecoupledConsensusModel.Protocol.token z)
        (Finset.mem_image_of_mem DecoupledConsensusModel.Protocol.token hz)
    have hyLe : y.round ≤ q := by
      have hlt := hyRoundLe
      rw [← hqc] at hlt
      exact Nat.le_of_lt_succ hlt
    exact Nat.le_antisymm hyLe hqLe
  obtain ⟨key, Head, hyconfirmed, hyfind, _, hBHead⟩ :=
    Proofs.HealingLemmas.exists_head_of_head_covers hcover
  have hyPool : y ∈
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc c p) w).st.core.toHealing.sg_votes q := by
    have hyraw := (Finset.mem_filter.mp hy).1
    simp only [DecoupledConsensusModel.Protocol.rawInputs, Finset.mem_filter] at hyraw
    obtain ⟨k, _, hyk⟩ := Finset.mem_biUnion.mp hyraw.1
    have hyRoundK := GradeDeliveryRun.projected_rounds_storeBeforeTime
      S adm.toNamedScheduleWellFormed w
        (DecoupledConsensusModel.Protocol.domain S.E S.hc c p) k y hyk
    have hkq : k = q := hyRoundK.symm.trans hyRound
    simpa only [hkq] using hyk
  have hySender : y.val_index = u := by
    have hyraw := (Finset.mem_filter.mp hy).1
    simp only [DecoupledConsensusModel.Protocol.rawInputs, Finset.mem_filter] at hyraw
    exact hyraw.2.1
  have hHeadT := rootCompatible_of_emittedSGHistory_at_read
    S adm hw hsg hyPool (hySender ▸ hu)
  have hheadRoot : Head.root = key := Proofs.HealingLemmas.find?_root hyfind
  have hyconfirmed' : y.confirmed = some Head.root := by
    rw [hheadRoot]
    exact hyconfirmed
  have hyfind' : Block.find?
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc c p) w).st.core.T
      Head.root = some Head := by
    rw [hheadRoot]
    exact hyfind
  change rootCompatible
    (NamedRun.stateBeforeTime S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc c p) w).st.core.T
    T y.confirmed = true at hHeadT
  rw [hyconfirmed'] at hHeadT
  change (match Block.find?
    (NamedRun.stateBeforeTime S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc c p) w).st.core.T Head.root with
    | some H => Block.compatible H T
    | none => true) = true at hHeadT
  rw [hyfind'] at hHeadT
  exact actionHistory_compatible_ancestor hBHead hHeadT

#print axioms phaseGrade_compatible_of_previousSGHistory_named

private theorem actionAnchor_cases_actionHistory
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    PhaseGrades.nodeAnchor S (actionReadAt S rho v r) r =
        Protocol.get_fg_root
          (actionReadAt S rho v r).st.core.toHealing.toFG ∨
      ∃ root A,
        (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v r).cache
          (actionReadAt S rho v r).st.core.toHealing r).g1 =
          some (some root) ∧
        DecoupledConsensusModel.Protocol.activePrefix
          (PhaseGrades.filteredTree (actionReadAt S rho v r)) root = some A ∧
        PhaseGrades.nodeAnchor S (actionReadAt S rho v r) r = A := by
  dsimp only [PhaseGrades.nodeAnchor, PhaseGrades.nodeRead]
  simp only [NamedProfile.gradeContract, DecoupledConsensusModel.Protocol.frameContract,
    DecoupledConsensusModel.Protocol.frameGradeRead]
  unfold DecoupledConsensusModel.Protocol.anchor
  cases hframe : (DecoupledConsensusModel.Protocol.readFrame
      (actionReadAt S rho v r).cache
      (actionReadAt S rho v r).st.core.toHealing r).g1 with
  | none => exact Or.inl rfl
  | some opt =>
      cases opt with
      | none => exact Or.inl rfl
      | some root =>
          cases hactive : DecoupledConsensusModel.Protocol.activePrefix
              (PhaseGrades.filteredTree (actionReadAt S rho v r)) root with
          | none => exact Or.inl (by simp only [hactive, Option.getD_none])
          | some A => exact Or.inr ⟨root, A, rfl, hactive, by
              simp only [hactive, Option.getD_some]⟩

private theorem activeActionAnchor_storeGrade_g1_actionHistory
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (hr : 0 < r) (hhor : S.a r ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) {root L : Block V}
    (hframe :
      (DecoupledConsensusModel.Protocol.readFrame
        (actionReadAt S rho w r).cache
        (actionReadAt S rho w r).st.core.toHealing r).g1 =
        some (some root))
    (hactive : DecoupledConsensusModel.Protocol.activePrefix
      (PhaseGrades.filteredTree (actionReadAt S rho w r)) root = some L) :
    PhaseGrades.storeGrade S.E S.hc
      (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st r .g1 L = true := by
  have hbase := actionFrame_g1 S adm.toNamedAdmissibleCore hw hr hhor
  cases hstore : PhaseGrades.storeRoot S.E S.hc
      (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st r .g1 with
  | none =>
      simp only [hstore, Option.map_none] at hbase
      rw [hframe] at hbase
      cases hbase
  | some raw =>
      have hrootEq : root = DecoupledConsensusModel.Protocol.clipGrade raw
          (actionReadAt S rho w r).st.core.F := by
        have hopt : some (some root) = some
            (some (DecoupledConsensusModel.Protocol.clipGrade raw
              (actionReadAt S rho w r).st.core.F)) :=
          hframe.symm.trans (by
            simpa only [hstore, Option.map_some] using hbase)
        exact Option.some.inj (Option.some.inj hopt)
      have hLroot : Block.Preceq L root := by
        unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
        exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
      have hLraw : Block.Preceq L raw := by
        rw [hrootEq] at hLroot
        exact Block.preceq_trans hLroot
          (NamedOutageClosure.q10_clip_preceq raw
            (actionReadAt S rho w r).st.core.F)
      have hrawGrade : PhaseGrades.phaseGrade S.E S.hc
          (PhaseGrades.readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
          (PhaseGrades.readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F
          r .g1 raw = true :=
        (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hstore)).2
      exact confirmation_phaseGrade_mono S.E S.hc _ _ r .g1
        hLraw hrawGrade

/-- earlier's one-round SG successor with the named prepared selector. The
relative G2 and active-G1 branches use the phase-ladder lemma above. -/
theorem sgEmissionsCompatible_succ_of_previousSGHistory_and_openingVotes_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {r : Round} {T : Block V}
    (hsg : HonestSGEmissionsCompatibleAtRound S rho r T)
    (hgf : NamedHonestVotesCone S rho (S.hc.opening_slot (r + 1))
      (fun X => Block.Preceq T X))
    (hpost : S.E.t_GST ≤ S.a r)
    (hhor : S.a (r + 1) ≤ rho.horizon)
    (hroots : ∀ w ∈ rho.honest, Block.compatible
      (Protocol.get_fg_root
        (actionStoreAt S rho w (r + 1)).st.core.toHealing.toFG) T = true) :
    HonestSGEmissionsCompatibleAtRound S rho (r + 1) T := by
  let c := r + 1
  have hc : 1 ≤ c := Nat.succ_le_succ (Nat.zero_le r)
  have hcPred : c - 1 = r := Nat.add_sub_cancel r 1
  have hmajority :=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow
  have hopenPost : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot (r + 1)) := by
    rw [← Protocol.Γ_1_eq_vote_time]
    exact hpost.trans ((le_add_of_nonneg_right S.E.Δ_pos.le).trans
      ((action_add_delta_le_next_Γ_neg1 S r).trans
        ((Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (r + 1)).le.trans
          (Γ_0_lt_Γ_1 S.hc S.E.Δ_pos (r + 1)).le)))
  have hconfHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot (r + 1)) ≤ rho.horizon := by
    rwa [opening_confirmation_time_eq_action]
  have hopen : 0 < S.hc.opening_slot (r + 1) :=
    Nat.mul_pos (Nat.succ_pos _) (Nat.zero_lt_of_lt S.hc.R_ge_two)
  have hheads : ∀ x ∈ rho.honest,
      x ∈ S.E.committee (S.hc.opening_slot (r + 1)) →
      Block.Preceq T
        (voterHeadAt S rho x (S.hc.opening_slot (r + 1))) := by
    intro x hx hxc
    obtain ⟨X, hTX, hXrun, hXemit⟩ := hgf x hx hxc
    obtain ⟨H, hHerase, hHrun, hHemit⟩ :=
      WeakGoldfish.voterHead_runBlock_and_emits
        S adm.toNamedAdmissibleCore hx hopen hxc
          ((vote_time_le_confirmation_time S.E _).trans hconfHor)
    have heq := Proofs.Optimistic.emits_gfVote_unique S
      adm.toNamedScheduleWellFormed hXemit hHemit rfl
    have hroot : X.root = H.root := by
      simpa only [Proofs.NamedWire.erase_root] using
        congrArg GoldfishVote.head heq
    have hXH : X = H :=
      adm.toNamedRootCollisionFree.root_injective X H hXrun hHrun
        X H (Or.inl (Proofs.NamedAncestry.named_self X))
          (Or.inr (Proofs.NamedAncestry.named_self H)) hroot
    rw [← hHerase, ← hXH]
    exact hTX
  intro w hw _
  have hrootT := hroots w hw
  have hliveT : Block.compatible
      (actionStoreAt S rho w c).live_confirmed T = true := by
    rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot S rho w c with
      ⟨C, hC, hClive⟩ | ⟨R, hRroot, hRlive⟩
    · rw [← hClive]
      simpa only [c, Block.compatible, Bool.or_comm] using
        (WeakGoldfish.genuineConfirmation_compatible_of_priorProtectedHeads
          S adm.toNamedAdmissibleCore hcom hw hopen hopenPost hconfHor
            hC hheads)
    · rw [← hRlive, hRroot]
      exact hrootT
  rcases (show Block.Preceq
      (Protocol.get_fg_root
        (actionStoreAt S rho w c).st.core.toHealing.toFG) T ∨
      Block.Preceq T
        (Protocol.get_fg_root
          (actionStoreAt S rho w c).st.core.toHealing.toFG) by
    simpa only [Block.compatible, Bool.or_eq_true] using hrootT) with
    hrootBelow | hTBelow
  · have hdomainHor : ∀ p : DecoupledConsensusModel.Protocol.Phase,
        DecoupledConsensusModel.Protocol.domain S.E S.hc c p ≤ rho.horizon := by
      intro p
      exact (FrameForward.domain_le_a S c p).trans
        (by simpa only [c] using hhor)
    have hFT : ∀ p : DecoupledConsensusModel.Protocol.Phase, Block.Preceq
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc c p) w).st.core.F T := by
      intro p
      have hdomainAction := FrameForward.domain_le_a S c p
      have hFmono : Block.Preceq
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc c p) w).st.core.F
          (NamedRun.stateBeforeTime S rho (S.a c) w).st.core.F := by
        rw [NamedOutageClosure.strict_read_eq_index S rho
              adm.toNamedScheduleWellFormed.sorted
              (DecoupledConsensusModel.Protocol.domain S.E S.hc c p),
            NamedOutageClosure.strict_read_eq_index S rho
              adm.toNamedScheduleWellFormed.sorted (S.a c)]
        exact Proofs.NamedRuntime.stateBefore_F_mono S rho w
          (NamedOutageClosure.strict_lengths_mono rho hdomainAction)
      have hFJ : Block.Preceq
          (actionStoreAt S rho w c).st.core.F
          (actionStoreAt S rho w c).st.core.J := by
        simpa only [actionStoreAt, actionReadAt,
          NamedActionReads.actionReadAt,
          NamedActionReads.actionReadFrom,
          NamedActionReads.confirmationReadFrom,
          NamedActionReads.preparedCache] using
            (Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
              S rho (S.a c) w)
      have hactionFroot : Block.Preceq
          (actionStoreAt S rho w c).st.core.F
          (Protocol.get_fg_root
            (actionStoreAt S rho w c).st.core.toHealing.toFG) :=
        StoreFinality.finalized_preceq_fgRoot hFJ
      have hpreFAction :
          (NamedRun.stateBeforeTime S rho (S.a c) w).st.core.F =
            (actionStoreAt S rho w c).st.core.F := by
        rfl
      exact Block.preceq_trans hFmono
        (Block.preceq_trans (hpreFAction ▸ hactionFroot) hrootBelow)
    have readyC : GradeRoundReady S rho c := by
      constructor
      · change S.E.t_GST ≤
          DecoupledConsensusModel.Protocol.early S.E S.hc (r + 1) .g2
        exact hpost.trans
          ((le_add_of_nonneg_right S.E.Δ_pos.le).trans
            (NamedOutageClosure.action_delta_le_early
              S S.hc.R_ge_three (Nat.lt_succ_self r)))
      · exact (FrameForward.domain_le_a S c .g0).trans
          (by simpa only [c] using hhor)
    have hanchorT : Block.compatible
        (PhaseGrades.nodeAnchor S (actionReadAt S rho w c) c) T = true := by
      rcases actionAnchor_cases_actionHistory S rho w c with
        hroot | ⟨root, L, hframe, hactive, hanchor⟩
      · rw [hroot]
        exact hrootT
      · rw [hanchor]
        have hLgrade := activeActionAnchor_storeGrade_g1_actionHistory
          S adm (Nat.zero_lt_of_lt hc)
            (by simpa only [c] using hhor) hw hframe hactive
        apply phaseGrade_compatible_of_previousSGHistory_named
          S adm hbelow hc (p := .g1) (by simpa only [hcPred] using hpost)
            (hdomainHor .g1) hw (hFT .g1) (by simpa only [hcPred] using hsg)
        simpa only [PhaseGrades.storeGrade, PhaseGrades.phaseGrade,
          PhaseGrades.readAt] using hLgrade
    rcases actionSGBlockAt_tiers S rho w c with
      hwalk | ⟨Q, hQ, hout⟩ | ⟨_, _, hout⟩ | ⟨_, _, hout⟩
    · exact actionHistory_compatible_ancestor hwalk.2.1 hliveT
    · rw [hout]
      have hQgrade := selectedQ2_storeGrade_at_g2Domain S adm hQ
      apply phaseGrade_compatible_of_previousSGHistory_named
        S adm hbelow hc (p := .g2) (by simpa only [hcPred] using hpost)
          (hdomainHor .g2) hw (hFT .g2) (by simpa only [hcPred] using hsg)
      simpa only [PhaseGrades.storeGrade, PhaseGrades.phaseGrade,
        PhaseGrades.readAt] using hQgrade
    · rw [hout]
      exact hrootT
    · rw [hout]
      exact hanchorT
  · have hrootVote := actionFGRoot_preceq_actionSGBlockAt S rho w c
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr (Block.preceq_trans hTBelow hrootVote)

#print axioms sgEmissionsCompatible_succ_of_previousSGHistory_and_openingVotes_named

/-- earlier's one-round FG-witness compatibility successor with the named
relative G2 selector discharged by the phase-ladder lemma. -/
theorem fgConfirmationWitness_compatible_of_previousSGHistory_and_openingVotes_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {r : Round} {T W : Block V}
    (hsg : HonestSGEmissionsCompatibleAtRound S rho r T)
    (hgf : NamedHonestVotesCone S rho (S.hc.opening_slot (r + 1))
      (fun X => Block.Preceq T X))
    (hprevPost : S.E.t_GST ≤ S.a r)
    (hpost : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot (r + 1)))
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot (r + 1)) ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest)
    (hroot : Block.compatible
      (Protocol.get_fg_root
        (actionStoreAt S rho w (r + 1)).st.core.toHealing.toFG) T = true)
    (hW : fgConfirmationWitness S
      (actionStoreAt S rho w (r + 1)) = some W) :
    Block.compatible W T = true := by
  let c := r + 1
  have hc : 1 ≤ c := Nat.succ_le_succ (Nat.zero_le r)
  have hcPred : c - 1 = r := Nat.add_sub_cancel r 1
  have hactionHor : S.a c ≤ rho.horizon := by
    simpa only [c, opening_confirmation_time_eq_action] using hhor
  have hliveT : Block.compatible
      (actionStoreAt S rho w c).live_confirmed T = true := by
    have hopen : 0 < S.hc.opening_slot c := by
      dsimp only [c]
      exact Nat.mul_pos (Nat.succ_pos _)
        (Nat.zero_lt_of_lt S.hc.R_ge_two)
    have hheads : ∀ x ∈ rho.honest,
        x ∈ S.E.committee (S.hc.opening_slot c) →
        Block.Preceq T
          (voterHeadAt S rho x (S.hc.opening_slot c)) := by
      intro x hx hxc
      obtain ⟨X, hTX, hXrun, hXemit⟩ := hgf x hx hxc
      obtain ⟨H, hHerase, hHrun, hHemit⟩ :=
        WeakGoldfish.voterHead_runBlock_and_emits
          S adm.toNamedAdmissibleCore hx hopen hxc
            ((vote_time_le_confirmation_time S.E _).trans hhor)
      have heq := Proofs.Optimistic.emits_gfVote_unique S
        adm.toNamedScheduleWellFormed hXemit hHemit rfl
      have hrootEq : X.root = H.root := by
        simpa only [Proofs.NamedWire.erase_root] using
          congrArg GoldfishVote.head heq
      have hXH : X = H :=
        adm.toNamedRootCollisionFree.root_injective X H hXrun hHrun
          X H (Or.inl (Proofs.NamedAncestry.named_self X))
            (Or.inr (Proofs.NamedAncestry.named_self H)) hrootEq
      rw [← hHerase, ← hXH]
      exact hTX
    rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot S rho w c with
      ⟨C, hC, hClive⟩ | ⟨R, hRroot, hRlive⟩
    · rw [← hClive]
      simpa only [Block.compatible, Bool.or_comm] using
        (WeakGoldfish.genuineConfirmation_compatible_of_priorProtectedHeads
          S adm.toNamedAdmissibleCore hcom hw hopen hpost hhor hC hheads)
    · rw [← hRlive, hRroot]
      simpa only [c] using hroot
  obtain ⟨Cfg, hsource, hWCfg⟩ := Option.map_eq_some_iff.mp hW
  have hsourceNode : PhaseGrades.nodeFGSource S
      (actionReadAt S rho w c) c = some Cfg := by
    have hsource' := hsource
    unfold actionFGSource at hsource'
    dsimp only at hsource'
    have hround : S.hc.round_of
        (actionStoreAt S rho w c).st.core.toHealing.s = c := by
      simpa only [Protocol.Store.toHealing] using
        actionStoreAt_round S rho w c
    rw [hround] at hsource'
    simpa only [PhaseGrades.nodeFGSource, PhaseGrades.nodeRead,
      actionStoreAt] using hsource'
  obtain ⟨Q, hQ⟩ : ∃ Q : Block V,
      PhaseGrades.nodeQ2 S (actionReadAt S rho w c) c = some Q := by
    cases hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho w c) c with
    | none =>
        have hbad := hsourceNode
        simp only [PhaseGrades.nodeFGSource, PhaseGrades.nodeQ2,
          PhaseGrades.nodeRead] at hbad hQ
        unfold Protocol.grade2_block_with at hbad
        rw [hQ] at hbad
        simp [Protocol.fg_source_with] at hbad
    | some Q => exact ⟨Q, rfl⟩
  have hrootQ : Block.Preceq
      (Protocol.get_fg_root
        (actionStoreAt S rho w c).st.core.toHealing.toFG) Q := by
    exact Proofs.Records.preceq_get_fg_root_of_mem_filtered
      (actionQ2_mem_filteredTree S rho w c hQ)
  have hQCfg : Block.Preceq Q Cfg :=
    preceq_actionFGSource_of_actionQ2 S rho w c hQ
      (Block.preceq_self Q) hsourceNode
  have hCfgT : Block.compatible Cfg T = true := by
    rcases (show Block.Preceq
        (Protocol.get_fg_root
          (actionStoreAt S rho w c).st.core.toHealing.toFG) T ∨
        Block.Preceq T
          (Protocol.get_fg_root
            (actionStoreAt S rho w c).st.core.toHealing.toFG) by
      simpa only [c, Block.compatible, Bool.or_eq_true] using hroot) with
      hrootBelow | hTBelow
    · have hdomainHor : DecoupledConsensusModel.Protocol.domain S.E S.hc c .g2 ≤
          rho.horizon :=
        (FrameForward.domain_le_a S c .g2).trans hactionHor
      have hFmono : Block.Preceq
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g2) w).st.core.F
          (NamedRun.stateBeforeTime S rho (S.a c) w).st.core.F := by
        rw [NamedOutageClosure.strict_read_eq_index S rho
              adm.toNamedScheduleWellFormed.sorted
              (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g2),
            NamedOutageClosure.strict_read_eq_index S rho
              adm.toNamedScheduleWellFormed.sorted (S.a c)]
        exact Proofs.NamedRuntime.stateBefore_F_mono S rho w
          (NamedOutageClosure.strict_lengths_mono rho
            (FrameForward.domain_le_a S c .g2))
      have hFJ : Block.Preceq
          (actionStoreAt S rho w c).st.core.F
          (actionStoreAt S rho w c).st.core.J := by
        simpa only [actionStoreAt, actionReadAt,
          NamedActionReads.actionReadAt,
          NamedActionReads.actionReadFrom,
          NamedActionReads.confirmationReadFrom,
          NamedActionReads.preparedCache] using
            (Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
              S rho (S.a c) w)
      have hactionFroot : Block.Preceq
          (actionStoreAt S rho w c).st.core.F
          (Protocol.get_fg_root
            (actionStoreAt S rho w c).st.core.toHealing.toFG) :=
        StoreFinality.finalized_preceq_fgRoot hFJ
      have hpreFAction :
          (NamedRun.stateBeforeTime S rho (S.a c) w).st.core.F =
            (actionStoreAt S rho w c).st.core.F := rfl
      have hFT : Block.Preceq
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g2) w).st.core.F T :=
        Block.preceq_trans hFmono
          (Block.preceq_trans (hpreFAction ▸ hactionFroot) hrootBelow)
      have hQgrade := selectedQ2_storeGrade_at_g2Domain S adm hQ
      have hQT : Block.compatible Q T = true := by
        apply phaseGrade_compatible_of_previousSGHistory_named
          S adm hbelow hc (p := .g2)
            (by simpa only [hcPred] using hprevPost)
            hdomainHor hw hFT (by simpa only [hcPred] using hsg)
        simpa only [PhaseGrades.storeGrade, PhaseGrades.phaseGrade,
          PhaseGrades.readAt] using hQgrade
      rcases actionFGSource_genuineClear_or_selectedG2_named
          S rho w c hQ hsource with hclear | hlocal
      · obtain ⟨C, _, hClive, _, _, hCfgC⟩ := hclear
        rw [hClive] at hCfgC
        exact actionHistory_compatible_ancestor hCfgC hliveT
      · subst Cfg
        exact hQT
    · simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr (Block.preceq_trans hTBelow
        (Block.preceq_trans hrootQ hQCfg))
  apply actionHistory_compatible_ancestor (B := Cfg) ?_ hCfgT
  rw [← hWCfg]
  obtain ⟨D, -, hDerase, hDderiv, -⟩ :=
    NamedActionSources.action_witness S rho w c Cfg hsource
  change ((actionReadAt S rho w c).st.core.σ Cfg).T_h ⪯ Cfg
  rw [hDderiv, ← hDerase]
  exact Proofs.Optimistic.derive_named_T_h_preceq S.E S.cfg D

#print axioms fgConfirmationWitness_compatible_of_previousSGHistory_and_openingVotes_named

/-- earlier's `checkpointVoteStep_of_actionHistories_of_frame`, with named
runtime objects and the prepared-anchor input derived internally. -/
theorem PrefixFGSelectorConeAt.checkpointVoteStep_of_actionHistories_of_frame_named
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T.erase)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (hc0 : c0 ≤ a.round)
    (ready : GradeRoundReady S rho a.round)
    (hpostPrev : S.E.t_GST ≤ S.a (a.round - 1))
    (hG1 : ∀ w ∈ rho.honest, ∃ Q : Block V,
      namedG1At S rho w a.round Q)
    (hpred : NamedOldTargetRootBelow S rho first blocked T)
    (hminimal : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ rho.honest →
      NamedRun.emits S rho b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) →
      a.round ≤ b.round)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hsourceRead : S.a a.round ≤ Protocol.vote_time S.E (s + 1))
    (hc : 1 ≤ S.hc.round_of (s + 1))
    (hsg : HonestSGEmissionsCompatibleAtRound S rho
      (S.hc.round_of (s + 1) - 1) T.erase)
    (hsgPost : S.E.t_GST ≤ S.a (S.hc.round_of (s + 1) - 1))
    (hhistory : ∀ r, a.round + 1 ≤ r →
      S.a r < Protocol.vote_time S.E (s + 1) →
      ∀ w ∈ rho.honest, ∀ W,
        fgConfirmationWitness S (actionStoreAt S rho w r) = some W →
          Block.compatible W T.erase = true)
    (hgf : NamedHonestVotesCone S rho s (fun X => Block.Preceq T.erase X)) :
    (∀ w ∈ rho.honest,
      Block.Preceq T.erase (voterHeadAt S rho w (s + 1))) ∧
      NamedHonestVotesCone S rho (s + 1)
        (fun X => Block.Preceq T.erase X) := by
  have hmajority :=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow
  have hroots : ∀ w ∈ rho.honest, Block.compatible
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w
          (s + 1)).st.core.toHealing.toFG) T.erase = true := by
    intro w hw
    simpa only [Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
      Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
      (hseed.fgRoot_compatible_of_recentWitnessHistory_of_frame_named
        adm hcom hbelow hfirst hframe hc0 ready hpostPrev hG1
          hpred hminimal hsourceRead hhistory hw)
  obtain ⟨K, _, hKT0, hKheight0, _, hKrun⟩ :=
    action_named_checkpoint S adm hseed.signerHonest hseed.sourceMem
  have hKT : K.erase = T.erase :=
    hKT0.trans hseed.checkpointDerived.symm
  have hKheight : (Protocol.derive_named S.E S.cfg K).h =
      blocked + 1 := hKheight0.trans hseed.sourceDerivedHeight
  have hwitnesses : ∀ w ∈ rho.honest, ∀ {C : NamedBlock V},
      C.erase = T.erase →
      (Protocol.derive_named S.E S.cfg C).h <
        (Internal.NamedRecoveryRead.voteDutyRead S rho w
          (s + 1)).st.core.h_max - 1 →
      RunBlock S rho C →
      ∀ (b : NamedAttestation V) (tb : Time) (J : NamedBlock V),
        b.val_index ∈ rho.honest →
        NamedRun.emits S rho b.val_index (Object.attest b) tb →
        tb < Protocol.vote_time S.E (s + 1) →
        b.height_pair.erase.height? =
          some ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).h_max - 1) →
        fgConfirmationWitness S
          (actionStoreAt S rho b.val_index b.round) =
            some (Protocol.derive_named S.E S.cfg J).T_h →
        RunBlock S rho J →
        Block.compatible C.erase
          (Protocol.derive_named S.E S.cfg J).T_h = true := by
    intro w hw C hCerase hhigh hCrun b tb J hb hemit htb hrow hselected _
    have hCK : C = K := by
      apply adm.toNamedRootCollisionFree.root_injective
        C K hCrun hKrun C K
          (Or.inl (Proofs.NamedAncestry.named_self C))
          (Or.inr (Proofs.NamedAncestry.named_self K))
      rw [← Proofs.NamedWire.erase_root C, hCerase, ← hKT,
        Proofs.NamedWire.erase_root]
    subst C
    by_cases hold : b.round < a.round + 1
    · have htime : tb ≤ S.a a.round := by
        rw [(Proofs.Optimistic.emits_attest_shape S hemit).2]
        exact Assembly.a_mono S (Nat.le_of_lt_succ hold)
      have hbound := honestEmittedHeight_le_honestHMaxBeforeTime
        S adm hb hemit hrow htime
      have hfloor : honestHMaxBeforeIndex S rho
          (strictEventIndex rho (S.a a.round)) ≤
            (Protocol.derive_named S.E S.cfg K).h := by
        rw [hKheight]
        exact hfirst.before _
          (hseed.actionPrefix_lt adm.toNamedScheduleWellFormed)
      have hrowLe :
          (Internal.NamedRecoveryRead.voteDutyRead S rho w
            (s + 1)).st.core.h_max - 1 ≤
            (Protocol.derive_named S.E S.cfg K).h := by
        have hbnd := hbound.trans hfloor
        simpa only [Internal.NamedRecoveryRead.voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
          Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hbnd
      exact False.elim ((Nat.not_lt_of_ge hrowLe) hhigh)
    · have hcompat := hhistory b.round (Nat.le_of_not_gt hold)
          (by simpa only [(Proofs.Optimistic.emits_attest_shape S hemit).2] using htb)
          b.val_index hb (Protocol.derive_named S.E S.cfg J).T_h hselected
      simpa only [hKT, Block.compatible, Bool.or_comm] using hcompat
  have hanchors : ∀ w ∈ rho.honest,
        Block.compatible (voterAnchorAt S rho w (s + 1)) T.erase = true := by
    intro w hw
    exact voterAnchorAt_compatible_of_previousSGHistory_named
      S adm hbelow hhor hc hsg hsgPost hw (hroots w hw)
  exact WeakGoldfish.goldfishCone_succ_of_runFrontierWitnesses
    S adm.toNamedAdmissibleCore hcom hmajority hs hpost hhor hgf
      hwitnesses hroots hanchors

#print axioms PrefixFGSelectorConeAt.checkpointVoteStep_of_actionHistories_of_frame_named

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
