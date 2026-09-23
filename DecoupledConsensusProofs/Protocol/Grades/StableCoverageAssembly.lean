module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.StableLaterConfirmation
public import DecoupledConsensusProofs.Protocol.Grades.ClaimOneClauseProducers
public import DecoupledConsensusProofs.Protocol.Handlers.StableOutputSeed

@[expose] public section

/-!
# Confirmation coverage from a stable root

This module relates the active G2 root at a confirmation read to its SG root
and proves `stableAt_confirmationCoverageBefore'`. The current-round frozen
G2 field requires a separate order argument at the endpoint `t = S.a s`;
later carrier induction alone does not give that direction.
-/

namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Internal.NamedOutageEntry Internal.NamedStableChainOutage
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]



private theorem coverage_domain_g0_lt_support_cutoff
    (S : Setup V) (q : Round) (u : Time)
    (hround : clockRoundAt S u = q)
    (hcut : u = Protocol.support_cutoff S.E (S.E.slotOf u)) :
    domain S.E S.hc q .g0 < u := by
  have hslot : S.hc.opening_slot q ≤ S.E.slotOf u := by
    rw [← hround]
    simp only [clockRoundAt, Protocol.HealConfig.opening_slot,
      Protocol.HealConfig.round_of]
    exact Nat.div_mul_le_self _ _
  have hcast : ((S.hc.opening_slot q : Nat) : Time) ≤
      ((S.E.slotOf u : Nat) : Time) := by
    exact_mod_cast hslot
  have hcoef : (0 : Time) ≤ 4 * S.E.Δ := by nlinarith [S.E.Δ_pos]
  have hmul := Int.mul_le_mul_of_nonneg_left hcast hcoef
  rw [hcut]
  unfold domain opening Protocol.proposal_time Protocol.support_cutoff Env.t slotStart
  simp only [Phase.domainOffset]
  push_cast at hmul ⊢
  nlinarith [S.E.Δ_pos]

/-- At a support-cutoff read, an active G2 candidate is below the same read's
SG anchor. This is row Q10 with the in-round frame-completion form, so it also
covers confirmation duties after the round action. -/
theorem activeG2_preceq_sgRoot_at_confirmation
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (w : V) (hw : w ∈ rho.honest) (q : Round) (hq : 0 < q)
    (u : Time) (hround : clockRoundAt S u = q)
    (hcut : u = Protocol.support_cutoff S.E (S.E.slotOf u))
    (hnext : u ≤ opening S.E S.hc (q + 1)) (hhor : u ≤ rho.horizon)
    {G : Block V} (hG : activeG2 S (confirmationReadAt S rho w u) = some G) :
    Block.Preceq G (sgRoot S (confirmationReadAt S rho w u)) := by
  let n := confirmationReadAt S rho w u
  have hg0lt : domain S.E S.hc q .g0 < u :=
    coverage_domain_g0_lt_support_cutoff S q u hround hcut
  have hdom0 : (0 : Time) ≤ domain S.E S.hc q .g0 := by
    have hopen0 := base_opening_nonneg S q
    unfold domain
    simp only [Phase.domainOffset]
    nlinarith [S.E.Δ_pos]
  have hu0 : (0 : Time) ≤ u := hdom0.trans hg0lt.le
  have hopen : opening S.E S.hc q < u := by
    rw [← hround]
    exact opening_lt_support_cutoff S u hu0 hcut
  have hg1lt : domain S.E S.hc q .g1 < u := by
    rw [domain_g1_eq_opening]
    exact hopen
  have hg2lt : domain S.E S.hc q .g2 < u :=
    (q10_domain_g2_lt_domain_g1 S q).trans hg1lt
  have hg0 := FrameCompleted.frame_phase_completed_in_round
    S rho core w hw q hq .g0 u hg0lt hnext (hg0lt.le.trans hhor)
  have hg1 := FrameCompleted.frame_phase_completed_in_round
    S rho core w hw q hq .g1 u hg1lt hnext (hg1lt.le.trans hhor)
  have hg2 := FrameCompleted.frame_phase_completed_in_round
    S rho core w hw q hq .g2 u hg2lt hnext (hg2lt.le.trans hhor)
  have hg0p := frame_phase_prepared_eq S rho w q .g0 u hround _ hg0
  have hg1p := frame_phase_prepared_eq S rho w q .g1 u hround _ hg1
  have hg2p := frame_phase_prepared_eq S rho w q .g2 u hround _ hg2
  have hreadRound : readRound S n = q := by
    simpa only [n, readRound_confirmationReadAt] using hround
  have hfr : readFrameAt S n =
      DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing q := by
    show DecoupledConsensusModel.Protocol.readFrame _ _ (readRound S n) = _
    rw [hreadRound]
  have hclosed : allClosed
      (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing q) = true := by
    simp only [allClosed, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Option.isSome_iff_exists.mpr ⟨_, hg0p⟩
    · exact Option.isSome_iff_exists.mpr ⟨_, hg1p⟩
    · exact Option.isSome_iff_exists.mpr ⟨_, hg2p⟩
  have hq2 : grade2Block n.st.core.toHealing
      (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing q) = some G := by
    rw [activeG2_eq, hfr] at hG
    unfold grade2Block
    rw [if_pos hclosed]
    exact hG
  have hFmono : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g1) w).st.core.F
      n.st.core.F := by
    change Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g1) w).st.core.F
      (NamedRun.stateBeforeTime S rho u w).st.core.F
    exact incl_strict_F_mono S rho core.toNamedScheduleWellFormed w hg1lt.le
  have hanchor := q10_frame_core S rho core w hw q hq n.st.core.toHealing
    (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing q)
    hFmono hg2p hg1p G hq2
  rw [sgRoot_eq, hfr, hreadRound]
  exact hanchor

#print axioms activeG2_preceq_sgRoot_at_confirmation

set_option maxHeartbeats 400000 in
/-- The corrected pre-boundary coverage clause. The stable round uses its
available G1 cross-reader floor. Later rounds re-grade the preceding honest
carrier floor at the current G2 domain and then use Q10. -/
theorem stableAt_confirmationCoverageBefore'
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s : Round) (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : NamedOutageEntry.SlashableBound S rho)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hstable : stableAt S rho v s P) (hs : 0 < s) :
    ConfirmationCoverageBefore' S rho b0 s P := by
  have hseed := outputSeed_of_stableAt
    S rho b0 b1 v s P hexec hslash hcom hsleep hforming hv hmargin hstable hs
  have hcap : b0 ≤ rho.horizon := hexec.interval.2.1.trans hexec.interval.2.2
  have hbase : HonestCarriersAbove S rho P s := hseed.carriers
  have hno : NoHonestConflictAbove S rho b0 P := hseed.noConflict
  have hcarriers := stableAt_honestCarriersAbove_before_boundary
    S rho b0 b1 v s P hexec hslash hcom hsleep hforming
      hv hmargin hseed hs
  obtain ⟨G0, raw0, hPG0, hG0raw0, hgrade1⟩ :=
    stableAt_rawG2_is_G1_everywhere
      S rho b0 b1 v s P hexec hslash hcom hsleep hforming
        hv hmargin hstable hs
  intro w hw t hst ht _hslot hcut
  have htHor : t ≤ rho.horizon := ht.le.trans hcap
  have hopenS : opening S.E S.hc s ≤ t := by
    rw [← domain_g1_eq_opening]
    exact (FrameForward.domain_le_a S s .g1).trans hst
  have hsq : s ≤ clockRoundAt S t :=
    succ_le_clockRound_of_opening S s t hopenS
  by_cases hqeq : clockRoundAt S t = s
  · by_cases hts : t = S.a s
    · subst t
      obtain ⟨_, raw, hPG, hGraw, hanchors⟩ :=
        stableAt_raw_preceq_actionAnchor
          S rho b0 b1 v s P hexec hslash hcom hsleep hforming
            hv hmargin hstable hs
      rw [← actionAnchor_eq_roundConfirmationSgRoot]
      exact Block.preceq_trans hPG (Block.preceq_trans hGraw (hanchors w hw))
    · have hstlt : S.a s < t := lt_of_le_of_ne hst (Ne.symm hts)
      have hgrid : OnDeltaGrid S t := by
        refine ⟨4 * ((S.E.slotOf t : Nat) : Int) + 2, ?_⟩
        exact hcut.trans (by
          unfold Protocol.support_cutoff Env.t slotStart
          ring)
      have hdeadline : S.a s + S.E.Δ ≤ t :=
        a_add_delta_le_of_lt_grid S t hgrid s hstlt
      obtain ⟨Pn, hPe, _, hheld⟩ :=
        NamedEarlyHolding.stable_prefix_held_before_boundary
          S rho b0 b1 hexec hsleep v hv s P hmargin hstable hno
            t hdeadline ht.le
      have hrow := NamedFGProtection.fg_protection_of_held_before_boundary
        S rho b0 b1 s hexec hmargin hsleep Pn
          (by simpa only [hPe] using hno) w hw t ht.le (hheld w hw)
      rcases hrow with hroot | htree
      · apply preceq_sgRoot_of_fg_root S (confirmationReadAt S rho w t)
        rw [prepared_root_eq]
        simpa only [hPe] using hroot
      · have hrawTree : raw0 ∈
            (readAt S rho (domain S.E S.hc s .g1) w).st.core.T :=
          namedG1At_mem_domainTree S rho (by
            simpa only [namedG1At] using hgrade1 w hw)
        obtain ⟨root1, hroot1, hrawRoot1⟩ := q10_freeze_of_graded S.E
          (readAt S rho (domain S.E S.hc s .g1) w).st.core.toHealing.gradeView
          (readAt S rho (domain S.E S.hc s .g1) w).st.core.F
          S.hc.η_SG s (q10_early_le_late S s .g1) hrawTree
          (by simpa only [storeGrade] using hgrade1 w hw)
        have hg1lt : domain S.E S.hc s .g1 < t := by
          rw [domain_g1_eq_opening]
          rw [← hqeq]
          exact opening_lt_support_cutoff S t
            ((Proofs.HealingLemmas.a_nonneg S s).trans hst) hcut
        have hnext : t ≤ opening S.E S.hc (s + 1) := by
          rw [← hqeq]
          exact (clockRound_lt_opening_succ S t).le
        have hg1 := FrameCompleted.frame_phase_completed_in_round
          S rho hexec.core w hw s hs .g1 t hg1lt hnext (hg1lt.le.trans htHor)
        rw [hroot1] at hg1
        have hg1p := frame_phase_prepared_eq S rho w s .g1 t hqeq _ hg1
        have htree' : P ∈ Protocol.get_filtered_block_tree
            (confirmationReadAt S rho w t).st.core.toHealing.toFG := by
          rw [prepared_tree_eq]
          simpa only [hPe] using htree
        have hcompat : Block.compatible P
            (NamedRun.stateBeforeTime S rho t w).st.core.F = true := by
          simp only [Block.compatible, Bool.or_eq_true]
          exact Or.inr (by simpa only [hPe, Protocol.Store.toHealing] using
            (q10_filtered_F htree))
        have hPclip : Block.Preceq P
            (DecoupledConsensusModel.Protocol.clipGrade root1
              (NamedRun.stateBeforeTime S rho t w).st.core.F) :=
          (q10_retained_prefix root1
            (NamedRun.stateBeforeTime S rho t w).st.core.F P hcompat).mpr
              (Block.preceq_trans (Block.preceq_trans hPG0 hG0raw0) hrawRoot1)
        apply preceq_sgRoot_of_g1 S (confirmationReadAt S rho w t)
          (by
            change (DecoupledConsensusModel.Protocol.readFrame
              (confirmationReadAt S rho w t).cache
              (confirmationReadAt S rho w t).st.core.toHealing
              (readRound S (confirmationReadAt S rho w t))).g1 = _
            rw [readRound_confirmationReadAt, hqeq]
            exact hg1p)
          htree'
        simpa only [NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom] using hPclip
  · have hsltq : s < clockRoundAt S t :=
      lt_of_le_of_ne hsq (Ne.symm hqeq)
    let r := clockRoundAt S t - 1
    have hqpos : 0 < clockRoundAt S t := hs.trans hsltq
    have hrsucc : r + 1 = clockRoundAt S t := by
      exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr hqpos)
    have hsr : s ≤ r := Nat.le_pred_of_lt hsltq
    have ht0 : (0 : Time) ≤ t := (Proofs.HealingLemmas.a_nonneg S s).trans hst
    have hopen : opening S.E S.hc (clockRoundAt S t) < t :=
      opening_lt_support_cutoff S t ht0 hcut
    have hdomainT : domain S.E S.hc (r + 1) .g2 < t := by
      rw [hrsucc]
      exact (q10_domain_g2_lt_domain_g1 S _).trans
        (by rw [domain_g1_eq_opening]; exact hopen)
    have hdomain : domain S.E S.hc (r + 1) .g2 < b0 :=
      hdomainT.trans ht
    have harlt : S.a r < b0 := by
      have hact : S.a r < domain S.E S.hc (r + 1) .g2 :=
        (lt_add_of_pos_right (S.a r) S.E.Δ_pos).trans_le
          ((action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r)).trans
            (early_le_domain S (r + 1)))
      exact hact.trans hdomain
    have hfloor : HonestCarriersAbove S rho P r := hcarriers r hsr harlt
    have hdeadline : S.a s + S.E.Δ ≤ domain S.E S.hc (r + 1) .g2 :=
      (Int.add_le_add_right (Assembly.a_mono S hsr) S.E.Δ).trans
        ((action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r)).trans
          (early_le_domain S (r + 1)))
    obtain ⟨Pn, hPe, _, hheld⟩ :=
      NamedEarlyHolding.stable_prefix_held_before_boundary
        S rho b0 b1 hexec hsleep v hv s P hmargin hstable hno
          t (hdeadline.trans hdomainT.le) ht.le
    have hrow := NamedFGProtection.fg_protection_of_held_before_boundary
      S rho b0 b1 s hexec hmargin hsleep Pn
        (by simpa only [hPe] using hno) w hw t ht.le (hheld w hw)
    rcases hrow with hroot | htree
    · apply preceq_sgRoot_of_fg_root S (confirmationReadAt S rho w t)
      rw [prepared_root_eq]
      simpa only [hPe] using hroot
    · have hFdomain : Block.Preceq
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc (r + 1) .g2) w).st.core.F P := by
        have hmono := incl_strict_F_mono S rho hexec.core.toNamedScheduleWellFormed w
          hdomainT.le
        exact Block.preceq_trans hmono (by
          simpa only [hPe, Protocol.Store.toHealing] using q10_filtered_F htree)
      have hgrade := storeGrade_g2_of_honestCarriers_before_boundary_domain
        S rho b0 b1 r P hexec hforming hdomain hfloor w hw hFdomain
      obtain ⟨Pm, hPme, _, hheldDomain⟩ :=
        NamedEarlyHolding.stable_prefix_held_before_boundary
          S rho b0 b1 hexec hsleep v hv s P hmargin hstable hno
            (domain S.E S.hc (r + 1) .g2) hdeadline hdomain.le
      have hPtree : P ∈ (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g2) w).st.core.T := by
        have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
          (domain S.E S.hc (r + 1) .g2) w).1.1.1
        rw [hcoh.1, ← hPme]
        exact Finset.mem_image_of_mem _ (hheldDomain w hw)
      obtain ⟨raw, hraw, hPraw⟩ := q10_freeze_of_graded S.E
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g2) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g2) w).st.core.F
        S.hc.η_SG (r + 1) (q10_early_le_late S (r + 1) .g2)
        hPtree hgrade
      have hnext : t ≤ opening S.E S.hc (r + 2) := by
        have hroundNext : r + 2 = clockRoundAt S t + 1 := by
          have h := congrArg (fun x : Nat => x + 1) hrsucc
          simpa only [Nat.add_assoc] using h
        rw [hroundNext]
        exact (clockRound_lt_opening_succ S t).le
      have hg2 := FrameCompleted.frame_phase_completed_in_round
        S rho hexec.core w hw (r + 1) (Nat.succ_pos r) .g2 t
          hdomainT hnext (hdomain.le.trans hcap)
      rw [hraw] at hg2
      have hg2p := frame_phase_prepared_eq S rho w (r + 1) .g2 t
        hrsucc.symm _ hg2
      have htree' : P ∈ Protocol.get_filtered_block_tree
          (confirmationReadAt S rho w t).st.core.toHealing.toFG := by
        rw [prepared_tree_eq]
        simpa only [hPe] using htree
      have hcompat : Block.compatible P
          (NamedRun.stateBeforeTime S rho t w).st.core.F = true := by
        simp only [Block.compatible, Bool.or_eq_true]
        exact Or.inr (by simpa only [hPe, Protocol.Store.toHealing] using
          (q10_filtered_F htree))
      have hPclip : Block.Preceq P
          (DecoupledConsensusModel.Protocol.clipGrade raw
            (NamedRun.stateBeforeTime S rho t w).st.core.F) :=
        (q10_retained_prefix raw
          (NamedRun.stateBeforeTime S rho t w).st.core.F P hcompat).mpr hPraw
      obtain ⟨G, hG, hPG⟩ := activeG2_covers S
        (confirmationReadAt S rho w t)
        (by
          change (DecoupledConsensusModel.Protocol.readFrame
            (confirmationReadAt S rho w t).cache
            (confirmationReadAt S rho w t).st.core.toHealing
            (readRound S (confirmationReadAt S rho w t))).g2 = _
          rw [readRound_confirmationReadAt, ← hrsucc]
          exact hg2p)
        htree' (by simpa only [NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom] using hPclip)
      exact Block.preceq_trans hPG
        (activeG2_preceq_sgRoot_at_confirmation
          S rho hexec.core w hw (r + 1) (Nat.succ_pos r) t hrsucc.symm hcut
            hnext htHor hG)

#print axioms stableAt_confirmationCoverageBefore'

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
