module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.StableOpeningConfirmationSafety
public import DecoupledConsensusProofs.Protocol.Grades.PrefixConfirmationSafety
public import DecoupledConsensusProofs.Execution.OutageResilienceRepairs
public import DecoupledConsensusProofs.Protocol.Grades.WeakBootstrapAction
public import DecoupledConsensusProofs.Protocol.Grades.WeakBootstrapSG
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Execution.PreparedReadBridge
public import DecoupledConsensusProofs.Execution.WeakConfirmationReadRootsCore

@[expose] public section

/-!
# Stable-round opening anchor and carrier floor

The completed G1 frame at the opening confirmation read selects either the
reader's FG root or an active prefix of a G1-graded root. Healthy-prefix
delivery and the grade-forming majority give every graded root an honest
previous-round SG carrier. The bounded protected-slot fold puts that carrier,
and the FG-root fallback, below every honest opening head.
-/

namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Internal.NamedOutageEntry Internal.NamedStableChainOutage
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol
open Proofs.HealingSurface Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem actionAnchor_eq_openingConfirmationAnchor
    (S : Setup V) (rho : NamedRun V) (v : V) (r : Round) :
    nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho v r) r =
      confirmationAnchorAt S rho v (S.hc.opening_slot r) := by
  have hcore := actionStoreAt_eq_update_confirmation_confStore S rho v r
  have hs : (actionStoreAt S rho v r).st.core.s =
      (confStore S rho v (S.hc.opening_slot r)).s := by
    rw [hcore]
    rfl
  have hround : S.hc.round_of
      (confStore S rho v (S.hc.opening_slot r)).s = r := by
    rw [← hs]
    exact actionStoreAt_round S rho v r
  have heq : nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho v r) r =
      confAnchorWith
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadAt S rho v (S.a r)).cache)
        S.E S.hc (confStore S rho v (S.hc.opening_slot r)) := by
    show ((NamedProfile.gradeContract (actionStoreAt S rho v r).cache).read
        S.E S.hc (actionStoreAt S rho v r).st.core.toHealing r).anchor = _
    rw [confAnchorWith, Protocol.get_sg_root_with, hround, hcore]
    rfl
  simpa only [confirmationAnchorAt, namedConfirmationAnchor, confAnchorWith,
    Internal.NamedRecoveryRead.confirmationInputRead,
    NamedActionReads.confirmationReadAt,
    Proofs.Optimistic.confStore_eq_confirmationInputRead,
    Proofs.HealingSurface.opening_confirmation_time_eq_action] using heq

/-- Public export of the action-anchor equality used by seed consumers. -/
theorem actionAnchor_eq_openingConfirmationAnchor_export
    (S : Setup V) (rho : NamedRun V) (v : V) (r : Round) :
    nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho v r) r =
      confirmationAnchorAt S rho v (S.hc.opening_slot r) := by
  exact actionAnchor_eq_openingConfirmationAnchor S rho v r

/-- Export the exact equality used by confirmation-coverage consumers. -/
theorem actionAnchor_eq_roundConfirmationSgRoot
    (S : Setup V) (rho : NamedRun V) (v : V) (r : Round) :
    nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho v r) r =
      sgRoot S (confirmationReadAt S rho v (S.a r)) := by
  rw [actionAnchor_eq_openingConfirmationAnchor]
  simp only [confirmationAnchorAt, namedConfirmationAnchor,
    Internal.NamedRecoveryRead.confirmationInputRead,
    Internal.NamedOutageEntry.confirmationReadAt,
    NamedActionReads.confirmationReadAt,
    Proofs.HealingSurface.opening_confirmation_time_eq_action, sgRoot]

#print axioms actionAnchor_eq_roundConfirmationSgRoot

/-- The G0 slot saved by an honest prepared action read is the G0-domain
freeze, clipped against the finalized block at the action read. -/
theorem actionRead_g0Root_eq_domainG0
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    {u : V} (hu : u ∈ rho.honest) {r : Round} (hr : 0 < r)
    (hhor : S.a r ≤ rho.horizon) :
    (DecoupledConsensusModel.Protocol.readFrame
        (Proofs.HealingSurface.actionReadAt S rho u r).cache
        (Proofs.HealingSurface.actionReadAt S rho u r).st.core.toHealing r).g0 =
      some ((storeRoot S.E S.hc
        (readAt S rho (domain S.E S.hc r .g0) u).st r .g0).map
          (fun B => DecoupledConsensusModel.Protocol.clipGrade B
            (Proofs.HealingSurface.actionReadAt S rho u r).st.core.F)) := by
  exact Proofs.HealingSurface.actionFrame_g0 S core hu hr hhor

#print axioms actionRead_g0Root_eq_domainG0

/-- The G1 slot saved by an honest prepared action read is the G1-domain
freeze, clipped against the finalized block at the action read. -/
theorem actionRead_g1Root_eq_domainG1
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    {u : V} (hu : u ∈ rho.honest) {r : Round} (hr : 0 < r)
    (hhor : S.a r ≤ rho.horizon) :
    (DecoupledConsensusModel.Protocol.readFrame
        (Proofs.HealingSurface.actionReadAt S rho u r).cache
        (Proofs.HealingSurface.actionReadAt S rho u r).st.core.toHealing r).g1 =
      some ((storeRoot S.E S.hc
        (readAt S rho (domain S.E S.hc r .g1) u).st r .g1).map
          (fun B => DecoupledConsensusModel.Protocol.clipGrade B
            (Proofs.HealingSurface.actionReadAt S rho u r).st.core.F)) := by
  exact Proofs.HealingSurface.actionFrame_g1 S core hu hr hhor

#print axioms actionRead_g1Root_eq_domainG1

private theorem actionRead_clear_of_domainG0Grade
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    {u : V} (hu : u ∈ rho.honest) {r : Round} (hr : 0 < r)
    (hhor : S.a r ≤ rho.horizon) {B : Block V}
    (hgrade : storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g0) u).st r .g0 B = true)
    (hactive : B ∈ filteredTree (Proofs.HealingSurface.actionReadAt S rho u r)) :
    nodeClear S (Proofs.HealingSurface.actionReadAt S rho u r) r B = true := by
  have hframe := actionRead_g0Root_eq_domainG0 S rho core hu hr hhor
  unfold nodeClear nodeRead
  change DecoupledConsensusModel.Protocol.clear
    (DecoupledConsensusModel.Protocol.readFrame
      (Proofs.HealingSurface.actionReadAt S rho u r).cache
      (Proofs.HealingSurface.actionReadAt S rho u r).st.core.toHealing r) B = true
  unfold DecoupledConsensusModel.Protocol.clear
  rw [hframe]
  cases hroot : storeRoot S.E S.hc
      (readAt S rho (domain S.E S.hc r .g0) u).st r .g0 with
  | none => rfl
  | some raw =>
      have hrawGrade : phaseGrade S.E S.hc
          (readAt S rho
            (domain S.E S.hc r .g0) u).st.core.toHealing.gradeView
          (readAt S rho (domain S.E S.hc r .g0) u).st.core.F
          r .g0 raw = true := by
        exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hroot)).2
      have hBGrade : phaseGrade S.E S.hc
          (readAt S rho
            (domain S.E S.hc r .g0) u).st.core.toHealing.gradeView
          (readAt S rho (domain S.E S.hc r .g0) u).st.core.F
          r .g0 B = true := by
        simpa only [storeGrade] using hgrade
      have hcompat : Block.compatible B raw = true :=
        Proofs.HealingLemmas.phaseGrade_g0_compatible S.E S.hc
          (readAt S rho
            (domain S.E S.hc r .g0) u).st.core.toHealing.gradeView
          (readAt S rho (domain S.E S.hc r .g0) u).st.core.F
          r B raw hBGrade hrawGrade
      have hFB : Block.Preceq
          (Proofs.HealingSurface.actionReadAt S rho u r).st.core.F B :=
        q10_filtered_F hactive
      change Block.compatible B
        (DecoupledConsensusModel.Protocol.clipGrade raw
          (Proofs.HealingSurface.actionReadAt S rho u r).st.core.F) = true
      simp only [Block.compatible, Bool.or_eq_true] at hcompat ⊢
      rcases hcompat with hBraw | hrawB
      · exact Or.inl ((q10_retained_prefix raw _ B (by
          simp only [Block.compatible, Bool.or_eq_true]
          exact Or.inr hFB)).mpr hBraw)
      · exact Or.inr (Block.preceq_trans (q10_clip_preceq raw _) hrawB)

private theorem stable_late_g0_public
    (S : Setup V) (r : Round) (hr : 0 < r) :
    PublicTime S (late S.E S.hc r .g0) := by
  have hslots : 2 ≤ r * S.hc.R :=
    S.hc.R_ge_two.trans (Nat.le_mul_of_pos_left S.hc.R hr)
  have hcoef : 3 ≤ 4 * (r * S.hc.R) := by
    calc
      3 ≤ 4 * 2 := by decide
      _ ≤ 4 * (r * S.hc.R) := Nat.mul_le_mul_left 4 hslots
  refine ⟨4 * (r * S.hc.R) - 3, ?_⟩
  unfold late opening Phase.lateOffset Protocol.proposal_time Env.t
    Protocol.HealConfig.opening_slot slotStart
  rw [Nat.cast_sub hcoef]
  push_cast
  ring

private theorem g1G0TwoCutoffDelivery_of_healthyPrefix
    (S : Setup V) {rho : NamedRun V} {r : Round} (cut : Time)
    (healthy : NamedHealthyPrefixDelivery S rho cut)
    (hcut : domain S.E S.hc r .g0 ≤ cut) :
    G1G0TwoCutoffDelivery S rho r where
  earlyAttest := by
    intro source hsource i a t hacc ht target htarget hmissing _
    have hdeadline : t + S.E.Δ ≤ cut := by
      apply (Int.add_lt_add_right ht S.E.Δ).le.trans
      have heq : early S.E S.hc r .g1 + S.E.Δ =
          early S.E S.hc r .g0 := by
        unfold early Phase.earlyOffset
        ring
      rw [heq]
      exact (by
        simp only [early, domain, Phase.earlyOffset, Phase.domainOffset]
        linarith [S.E.Δ_pos] : early S.E S.hc r .g0 ≤ domain S.E S.hc r .g0).trans hcut
    obtain ⟨t', hlo, hhi, j, hcall⟩ :=
      healthy.relay_attest source hsource i a t hacc target htarget hmissing hdeadline rfl
    refine ⟨t', hlo, ?_, j, hcall⟩
    calc
      t' < t + S.E.Δ := hhi
      _ < early S.E S.hc r .g1 + S.E.Δ := Int.add_lt_add_right ht S.E.Δ
      _ = early S.E S.hc r .g0 := by
        unfold early Phase.earlyOffset
        ring
  lateAttest := by
    intro source hsource i a t hacc ht target htarget hmissing _
    have hdeadline : t + S.E.Δ ≤ cut := by
      apply (Int.add_lt_add_right ht S.E.Δ).le.trans
      have heq : late S.E S.hc r .g0 + S.E.Δ =
          late S.E S.hc r .g1 := by
        unfold late Phase.lateOffset
        ring
      rw [heq]
      exact (by
        simp only [late, domain, Phase.lateOffset, Phase.domainOffset]
        linarith [S.E.Δ_pos] : late S.E S.hc r .g1 ≤ domain S.E S.hc r .g0).trans hcut
    obtain ⟨t', hlo, hhi, j, hcall⟩ :=
      healthy.relay_attest source hsource i a t hacc target htarget hmissing hdeadline rfl
    refine ⟨t', hlo, ?_, j, hcall⟩
    calc
      t' < t + S.E.Δ := hhi
      _ < late S.E S.hc r .g0 + S.E.Δ := Int.add_lt_add_right ht S.E.Δ
      _ = late S.E S.hc r .g1 := by
        unfold late Phase.lateOffset
        ring

private theorem sameReaderG1G0BodyReadyGuard_of_actionActive
    (S : Setup V) {rho : NamedRun V} (core : NamedAdmissibleCore S rho)
    {r : Round} (hr : 0 < r) {u : V} (hu : u ∈ rho.honest)
    {B : Block V}
    (hactive : B ∈ filteredTree (Proofs.HealingSurface.actionReadAt S rho u r)) :
    G1G0CrossReaderBodyReadyGuard S rho r u u B := by
  have hF0action : Block.Preceq
      (readAt S rho (domain S.E S.hc r .g0) u).st.core.F
      (Proofs.HealingSurface.actionReadAt S rho u r).st.core.F := by
    show Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g0) u).st.core.F
      (NamedRun.stateBeforeTime S rho (S.a r) u).st.core.F
    rw [strict_read_eq_index S rho core.sorted (domain S.E S.hc r .g0),
      strict_read_eq_index S rho core.sorted (S.a r)]
    exact Proofs.NamedRuntime.stateBefore_F_mono S rho u
      (strict_lengths_mono rho (FrameForward.domain_le_a S r .g0))
  have hF0B : Block.Preceq
      (readAt S rho (domain S.E S.hc r .g0) u).st.core.F B :=
    Block.preceq_trans hF0action (q10_filtered_F hactive)
  have hF10 : Block.Preceq
      (readAt S rho (domain S.E S.hc r .g1) u).st.core.F
      (readAt S rho (domain S.E S.hc r .g0) u).st.core.F := by
    change Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) u).st.core.F
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g0) u).st.core.F
    rw [strict_read_eq_index S rho core.sorted (domain S.E S.hc r .g1),
      strict_read_eq_index S rho core.sorted (domain S.E S.hc r .g0)]
    apply Proofs.NamedRuntime.stateBefore_F_mono S rho u
    apply strict_lengths_mono rho
    simp only [domain, Phase.domainOffset]
    linarith [S.E.Δ_pos]
  refine ⟨?_, ?_⟩
  · intro sender x hx hcover
    change x ∈ interpretedInputs
      (readAt S rho (domain S.E S.hc r .g1) u).st.core.toHealing.gradeView
      (readAt S rho (domain S.E S.hc r .g1) u).st.core.F
      S.hc.η_SG r (early S.E S.hc r .g1) sender at hx
    change DecoupledConsensusModel.Protocol.localCovers
      (readAt S rho (domain S.E S.hc r .g1) u).st.core.toHealing.gradeView
      x.confirmed B = true at hcover
    change DecoupledConsensusModel.Protocol.bodyReady
      (readAt S rho (domain S.E S.hc r .g0) u).st.core.toHealing.gradeView
      (readAt S rho (domain S.E S.hc r .g0) u).st.core.F
      (early S.E S.hc r .g0) x = true
    obtain ⟨-, hready⟩ := Finset.mem_filter.mp hx
    cases hconf : x.confirmed with
    | none => simp [DecoupledConsensusModel.Protocol.bodyReady, hconf]
    | some root =>
        simp only [DecoupledConsensusModel.Protocol.bodyReady, hconf] at hready ⊢
        simp only [Protocol.HealingStore.gradeView, Protocol.Store.toHealing] at hready ⊢
        cases hfind : Block.find?
            (readAt S rho (domain S.E S.hc r .g1) u).st.core.T root with
        | none => rw [hfind] at hready; exact absurd hready (by simp)
        | some H =>
            rw [hfind] at hready
            simp only [Bool.and_eq_true] at hready
            obtain ⟨hstamp, -⟩ := hready
            have hHtree : H ∈
                (readAt S rho (domain S.E S.hc r .g1) u).st.core.T :=
              Proofs.HealingLemmas.find?_mem hfind
            have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
              (domain S.E S.hc r .g1) u).1.1.1
            rw [hcoh.1] at hHtree
            obtain ⟨Hn, hHbody, hHnErase⟩ := Finset.mem_image.mp hHtree
            have hHearly : Hn ∈ (NamedRun.stateBeforeTime S rho
                (early S.E S.hc r .g1) u).st.bodies := by
              apply NamedPublicCutBody.body_mem_stateBeforeTime_of_public_stampedBefore
                S rho core.toNamedScheduleWellFormed
                (q10_early_g1_public S r hr) hHbody
              simpa only [hHnErase] using hstamp
            have hcarry := q10_strict_body_carry S rho
              core.toNamedScheduleWellFormed u
              (c := early S.E S.hc r .g1)
              (d := domain S.E S.hc r .g0)
              (by
                simp only [early, domain, Phase.earlyOffset, Phase.domainOffset]
                linarith [S.E.Δ_pos]) hHearly
            have hstampTarget : stampedBefore
                (readAt S rho
                  (domain S.E S.hc r .g0) u).st.core.timestamp_block
                (early S.E S.hc r .g0) Hn.erase = true := by
              have hstampEarly :=
                NamedBlockStamp.held_body_stampedBefore_stateBeforeTime
                  S rho core.toNamedScheduleWellFormed u
                    (early S.E S.hc r .g1) Hn hHearly
              unfold stampedBefore at hstampEarly ⊢
              rw [hcarry.2]
              exact GradeCutoffMono.stampedBefore_mono _ (by
                simp only [early, Phase.earlyOffset]
                linarith [S.E.Δ_pos]) hstampEarly
            have hfindTarget : Block.find?
                (readAt S rho (domain S.E S.hc r .g0) u).st.core.T Hn.erase.root =
                some Hn.erase := by
              exact NamedOutageClosure.held_find_at_strict
                S rho core.toNamedScheduleWellFormed
                  core.toNamedRootCollisionFree u hu _ Hn hcarry.1
            have hroot : Hn.root = root := by
              rw [← Proofs.NamedWire.erase_root, hHnErase]
              exact Proofs.HealingLemmas.find?_root hfind
            have hBH : Block.Preceq B Hn.erase := by
              unfold DecoupledConsensusModel.Protocol.localCovers Protocol.head_covers at hcover
              simp only [Protocol.HealingStore.gradeView, Protocol.Store.toHealing, hconf] at hcover
              rw [hfind] at hcover
              simpa only [hHnErase] using hcover
            have hfindTarget' : Block.find?
                (readAt S rho (domain S.E S.hc r .g0) u).st.core.T Hn.root =
                some Hn.erase := by
              simpa only [Proofs.NamedWire.erase_root] using hfindTarget
            change (match Block.find?
              (readAt S rho (domain S.E S.hc r .g0) u).st.core.T root with
              | none => false
              | some head => stampedBefore
                  (readAt S rho
                    (domain S.E S.hc r .g0) u).st.core.timestamp_block
                  (early S.E S.hc r .g0) head &&
                Block.compatible head
                  (readAt S rho (domain S.E S.hc r .g0) u).st.core.F) = true
            rw [← hroot, hfindTarget', Bool.and_eq_true]
            refine ⟨hstampTarget, ?_⟩
            simp only [Block.compatible, Bool.or_eq_true]
            exact Or.inr (Block.preceq_trans hF0B hBH)
  · intro sender x hx
    change x ∈ interpretedInputs
      (readAt S rho (domain S.E S.hc r .g0) u).st.core.toHealing.gradeView
      (readAt S rho (domain S.E S.hc r .g0) u).st.core.F
      S.hc.η_SG r (late S.E S.hc r .g0) sender at hx
    change DecoupledConsensusModel.Protocol.bodyReady
      (readAt S rho (domain S.E S.hc r .g1) u).st.core.toHealing.gradeView
      (readAt S rho (domain S.E S.hc r .g1) u).st.core.F
      (late S.E S.hc r .g1) x = true
    obtain ⟨-, hready⟩ := Finset.mem_filter.mp hx
    cases hconf : x.confirmed with
    | none => simp [DecoupledConsensusModel.Protocol.bodyReady, hconf]
    | some root =>
        simp only [DecoupledConsensusModel.Protocol.bodyReady, hconf] at hready ⊢
        simp only [Protocol.HealingStore.gradeView, Protocol.Store.toHealing] at hready ⊢
        cases hfind : Block.find?
            (readAt S rho (domain S.E S.hc r .g0) u).st.core.T root with
        | none => rw [hfind] at hready; exact absurd hready (by simp)
        | some H =>
            rw [hfind] at hready
            simp only [Bool.and_eq_true] at hready
            obtain ⟨hstamp, hcompat0⟩ := hready
            have hHtree : H ∈
                (readAt S rho (domain S.E S.hc r .g0) u).st.core.T :=
              Proofs.HealingLemmas.find?_mem hfind
            have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
              (domain S.E S.hc r .g0) u).1.1.1
            rw [hcoh.1] at hHtree
            obtain ⟨Hn, hHbody, hHnErase⟩ := Finset.mem_image.mp hHtree
            have hHlate : Hn ∈ (NamedRun.stateBeforeTime S rho
                (late S.E S.hc r .g0) u).st.bodies := by
              apply NamedPublicCutBody.body_mem_stateBeforeTime_of_public_stampedBefore
                S rho core.toNamedScheduleWellFormed
                (stable_late_g0_public S r hr) hHbody
              simpa only [hHnErase] using hstamp
            have hcarry := q10_strict_body_carry S rho
              core.toNamedScheduleWellFormed u
              (c := late S.E S.hc r .g0)
              (d := domain S.E S.hc r .g1)
              (by
                simp only [late, domain, Phase.lateOffset, Phase.domainOffset]
                linarith [S.E.Δ_pos]) hHlate
            have hstampSource : stampedBefore
                (readAt S rho
                  (domain S.E S.hc r .g1) u).st.core.timestamp_block
                (late S.E S.hc r .g1) Hn.erase = true := by
              have hstampLate :=
                NamedBlockStamp.held_body_stampedBefore_stateBeforeTime
                  S rho core.toNamedScheduleWellFormed u
                    (late S.E S.hc r .g0) Hn hHlate
              unfold stampedBefore at hstampLate ⊢
              rw [hcarry.2]
              exact GradeCutoffMono.stampedBefore_mono _ (by
                simp only [late, Phase.lateOffset]
                linarith [S.E.Δ_pos]) hstampLate
            have hfindSource : Block.find?
                (readAt S rho (domain S.E S.hc r .g1) u).st.core.T Hn.erase.root =
                some Hn.erase := by
              exact NamedOutageClosure.held_find_at_strict
                S rho core.toNamedScheduleWellFormed
                  core.toNamedRootCollisionFree u hu _ Hn hcarry.1
            have hroot : Hn.root = root := by
              rw [← Proofs.NamedWire.erase_root, hHnErase]
              exact Proofs.HealingLemmas.find?_root hfind
            have hcompat1 : Block.compatible Hn.erase
                (readAt S rho (domain S.E S.hc r .g1) u).st.core.F = true := by
              rw [hHnErase]
              simp only [Block.compatible, Bool.or_eq_true] at hcompat0 ⊢
              rcases hcompat0 with hHF0 | hF0H
              · exact (Block.preceq_linear hHF0 hF10).elim Or.inl Or.inr
              · exact Or.inr (Block.preceq_trans hF10 hF0H)
            have hfindSource' : Block.find?
                (readAt S rho (domain S.E S.hc r .g1) u).st.core.T Hn.root =
                some Hn.erase := by
              simpa only [Proofs.NamedWire.erase_root] using hfindSource
            change (match Block.find?
              (readAt S rho (domain S.E S.hc r .g1) u).st.core.T root with
              | none => false
              | some head => stampedBefore
                  (readAt S rho
                    (domain S.E S.hc r .g1) u).st.core.timestamp_block
                  (late S.E S.hc r .g1) head &&
                Block.compatible head
                  (readAt S rho (domain S.E S.hc r .g1) u).st.core.F) = true
            rw [← hroot, hfindSource', Bool.and_eq_true]
            exact ⟨hstampSource, hcompat1⟩

private theorem storeGrade_g0_of_sameReader_g1_healthyPrefix
    (S : Setup V) {rho : NamedRun V} (core : NamedAdmissibleCore S rho)
    {r : Round} (hr : 0 < r) (cut : Time)
    (healthy : NamedHealthyPrefixDelivery S rho cut)
    (hcut : domain S.E S.hc r .g0 ≤ cut)
    (hhor : domain S.E S.hc r .g0 ≤ rho.horizon)
    {u : V} (hu : u ∈ rho.honest) {B : Block V}
    (hG1 : storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g1) u).st r .g1 B = true)
    (hactive : B ∈ filteredTree (Proofs.HealingSurface.actionReadAt S rho u r)) :
    storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g0) u).st r .g0 B = true := by
  exact storeGrade_g0_of_storeGrade_g1_cross_reader
    S rho core r
      (g1G0TwoCutoffDelivery_of_healthyPrefix S cut healthy hcut)
      hhor u u hu hu B hG1
      (sameReaderG1G0BodyReadyGuard_of_actionActive S core hr hu hactive)

private theorem activeActionAnchor_storeGrade_g1
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {r : Round} (hr : 0 < r) (hhor : S.a r ≤ rho.horizon)
    {u : V} (hu : u ∈ rho.honest) {root A : Block V}
    (hframe :
      (DecoupledConsensusModel.Protocol.readFrame
        (Proofs.HealingSurface.actionReadAt S rho u r).cache
        (Proofs.HealingSurface.actionReadAt S rho u r).st.core.toHealing r).g1 =
          some (some root))
    (hactive : DecoupledConsensusModel.Protocol.activePrefix
      (filteredTree (Proofs.HealingSurface.actionReadAt S rho u r)) root = some A) :
    storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g1) u).st r .g1 A = true := by
  have hreadFrame := Proofs.HealingSurface.actionFrame_g1 S core hu hr hhor
  cases hstore : storeRoot S.E S.hc
      (readAt S rho (domain S.E S.hc r .g1) u).st r .g1 with
  | none =>
      simp only [hstore, Option.map_none] at hreadFrame
      rw [hframe] at hreadFrame
      cases hreadFrame
  | some raw =>
      have hrootEq : root = DecoupledConsensusModel.Protocol.clipGrade raw
          (Proofs.HealingSurface.actionReadAt S rho u r).st.core.F := by
        have hopt : some (some root) = some
            (some (DecoupledConsensusModel.Protocol.clipGrade raw
              (Proofs.HealingSurface.actionReadAt S rho u r).st.core.F)) :=
          hframe.symm.trans (by
            simpa only [hstore, Option.map_some] using hreadFrame)
        exact Option.some.inj (Option.some.inj hopt)
      have hAroot : Block.Preceq A root := by
        unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
        exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
      have hAraw : Block.Preceq A raw := by
        rw [hrootEq] at hAroot
        exact Block.preceq_trans hAroot (q10_clip_preceq raw _)
      have hrawGrade : phaseGrade S.E S.hc
          (readAt S rho
            (domain S.E S.hc r .g1) u).st.core.toHealing.gradeView
          (readAt S rho (domain S.E S.hc r .g1) u).st.core.F
          r .g1 raw = true := by
        exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hstore)).2
      exact Proofs.HealingSurface.confirmation_phaseGrade_mono S.E S.hc _ _ r .g1
        hAraw hrawGrade


set_option maxHeartbeats 400000 in
/-- Every honest opening head extends every honest reader's prepared opening
confirmation anchor. -/
theorem openingHeads_above_confirmationAnchors
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (s : Round)
    (hexec : OutageExecution S rho b0 b1)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hmargin : FormationMargin S s b0) (hs : 0 < s) :
    ∀ u ∈ rho.honest, ∀ w ∈ rho.honest,
      Block.Preceq
        (confirmationAnchorAt S rho u (S.hc.opening_slot s))
        (voterHeadAt S rho w (S.hc.opening_slot s)) := by
  have hcapHor : b0 ≤ rho.horizon :=
    hexec.interval.2.1.trans hexec.interval.2.2
  have hasCap : S.a s ≤ b0 :=
    (Assembly.a_mono S (Nat.le_succ s)).trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin)
  have hroundOne : domain S.E S.hc 1 .g2 ≤ b0 := by
    exact (FrameForward.domain_le_a S 1 .g2).trans
      ((Assembly.a_mono S (Nat.succ_le_succ (Nat.zero_le s))).trans
        ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin))
  have hT1 := protectedVoteSlots_before
    S rho b0 b1 hexec hcom hsleep hroundOne
  let d := S.hc.opening_slot s
  have hd : 1 ≤ d := by
    dsimp only [d, Protocol.HealConfig.opening_slot]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hs.ne' (Nat.ne_of_gt
      (Nat.zero_lt_of_lt S.hc.R_ge_two)))
  have hdCap : Protocol.vote_time S.E d + S.E.Δ ≤ b0 := by
    rw [Proofs.Optimistic.vote_time_add_delta]
    exact (Protocol.support_cutoff_le_confirmation_time S.E d).trans
      (by simpa only [d, Proofs.HealingSurface.opening_confirmation_time_eq_action] using hasCap)
  intro u hu w hw
  have hsources := actionSources_preceq_voteDutyHead_before_of_T1
    S rho b0 b1 hexec hcom hsleep hroundOne hT1 hd hdCap hw
  have hsourceTime : ∀ k, k < s → S.a k < Protocol.vote_time S.E (d + 1) := by
    intro k hk
    exact (Int.lt_add_of_pos_right _ S.E.Δ_pos).trans_le
      ((Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt S hk).trans
        ((Protocol.proposal_time_lt_vote_time S.E d).le.trans
          (Protocol.vote_time_mono_slots S.E (Nat.le_succ d))))
  have hmajority : HonestWeightMajority S rho.honest := by
    apply WeakSG.honestWeightMajority_of_awakeWindowMajority S
    exact hsleep s hs (Or.inl ⟨Proofs.HealingLemmas.a_nonneg S s,
      hasCap.trans hcapHor⟩)
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.confirmationInputRead S rho u d).st.core.toHealing.toFG)
      (voterHeadAt S rho w d) := by
    let t := Protocol.confirmation_time S.E d
    rcases WeakFG.fgRoot_confirmationWitness_at_read
        S hexec.core hmajority hu t with hgen | ⟨C, -, -, a, ta, ha, hemit, hat, -, hT⟩
    · have hgen' : Protocol.get_fg_root
          (Internal.NamedRecoveryRead.confirmationInputRead S rho u d).st.core.toHealing.toFG =
          Block.genesis := by
        simpa only [t, Internal.NamedRecoveryRead.confirmationInputRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hgen
      rw [hgen']
      exact Protocol.preceq_genesis _
    · have htime : ta = S.a a.round := (emits_attest_shape S hemit).2
      have haTime : S.a a.round < Protocol.vote_time S.E (d + 1) := by
        apply (Proofs.HealingSurface.action_time_lt_proposal_of_lt_previous_confirmation
          S (Nat.zero_lt_succ d) ?_).trans
          (Protocol.proposal_time_lt_vote_time S.E (d + 1))
        rw [← htime]
        simpa only [Nat.add_sub_cancel] using hat
      have hbound := ((hsources a.round haTime).2 a.val_index ha).2 _ hT
      simpa only [t, Internal.NamedRecoveryRead.confirmationInputRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hbound
  rcases confirmationAnchorAt_cases S rho u d with hfg | ⟨raw, A, hframe, hactive, hA⟩
  · rw [hfg]
    exact hroot
  · rw [hA]
    have hround : S.hc.round_of (S.E.slotOf (S.a s)) = s :=
      Proofs.HealingLemmas.round_of_slotOf_a S s
    have hdomain : domain S.E S.hc s .g1 < S.a s := by
      rw [NamedOutageClosure.domain_g1_eq_opening,
        DecoupledConsensusModel.Protocol.opening, ← Protocol.Γ_0_eq_proposal_time,
        ← Proofs.HealingSurface.opening_confirmation_time_eq_action]
      exact (Protocol.proposal_time_lt_vote_time S.E d).trans_le
        (Protocol.vote_time_le_confirmation_time S.E d)
    have hreadRound : S.hc.round_of
        (Internal.NamedRecoveryRead.confirmationInputRead S rho u d).st.core.s = s := by
      simpa only [d, Internal.NamedRecoveryRead.confirmationInputRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Proofs.HealingSurface.opening_confirmation_time_eq_action,
        Protocol.NamedStore.setClock] using Proofs.HealingLemmas.round_of_slotOf_a S s
    rw [hreadRound] at hframe
    have hgrade := WeakSG.phaseGrade_of_preparedFrame_g1
      S rho hexec.core u hu s hs (S.a s) hround hdomain
      (FrameForward.a_lt_opening_succ S s).le
      (hdomain.le.trans (hasCap.trans hcapHor))
      (by simpa only [d, Internal.NamedRecoveryRead.confirmationInputRead,
        NamedActionReads.confirmationReadAt,
        Proofs.HealingSurface.opening_confirmation_time_eq_action] using hframe)
    have hwindow : RelativeCarrierWindowAt S rho (s - 1) .g1 := by
      intro reader hreader x hx
      change ∃ y ∈ interpretedInputs
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc ((s - 1) + 1) .g1) reader).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc ((s - 1) + 1) .g1) reader).st.core.F
          S.hc.η_SG ((s - 1) + 1) (early S.E S.hc ((s - 1) + 1) .g1) x,
        y.round = s - 1 ∧
        y.confirmed = some (actionSGBlockAt S rho x (s - 1)).root ∧
        Block.find?
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc ((s - 1) + 1) .g1) reader).st.core.T
          (actionSGBlockAt S rho x (s - 1)).root =
            some (actionSGBlockAt S rho x (s - 1))
      simp only [Nat.sub_add_cancel hs]
      obtain ⟨hxHon, a, hax, haround, hemit⟩ :=
        (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho x (s - 1)).mp hx
      have hxAwake : (S.node x).awake (s - 1) = true := by
        simpa only [haround] using emits_attest_awake S hemit
      have hactionHor : S.a (s - 1) ≤ rho.horizon :=
        (Assembly.a_mono S (Nat.sub_le s 1)).trans (hasCap.trans hcapHor)
      have hemitAction := honest_emits_exact_actionAttestationAt_of_awake
        S hexec.core.toNamedScheduleWellFormed hxHon (s - 1) hxAwake hactionHor
      obtain ⟨i, hi, -, hbody⟩ :=
        Proofs.NamedOutageInputs.emitted_attestation_head S rho hemitAction
      dsimp at hbody
      obtain ⟨H, hH, hconfirmed⟩ := hbody
      have hstate := NamedActionSources.action_read_index S rho
        hexec.core.toNamedScheduleWellFormed i x (s - 1) hi
      have hHsource : H ∈
          (NamedRun.stateBeforeTime S rho (S.a (s - 1)) x).st.bodies := by
        rw [← hstate]
        exact hH
      have hHrun : RunBlock S rho H :=
        Proofs.Bridges.runBlock_of_stateBefore_mem S hxHon hH
      have hcarrierMem : actionSGBlockAt S rho x (s - 1) ∈
          (NamedRun.stateBeforeTime S rho (S.a (s - 1)) x).st.core.T :=
        actionSGBlockAt_mem_storeBeforeTime S rho x (s - 1)
      obtain ⟨D, hDbody, hDerase⟩ :=
        Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
          (S.a (s - 1)) x hcarrierMem
      obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
        S rho hexec.core.sorted (S.a (s - 1))
      have hDprefix : D ∈ (NamedRun.stateBefore S rho n x).st.bodies := by
        rw [← hn]
        exact hDbody
      have hHprefix : H ∈ (NamedRun.stateBefore S rho n x).st.bodies := by
        rw [← hn]
        exact hHsource
      have hDrun : RunBlock S rho D := Proofs.Bridges.runBlock_of_stateBefore_mem S hxHon hDprefix
      have hHrun' : RunBlock S rho H := Proofs.Bridges.runBlock_of_stateBefore_mem S hxHon hHprefix
      have hrootEq : D.root = H.root := by
        rw [← Proofs.NamedWire.erase_root D, hDerase]
        exact Option.some.inj ((actionAttestationAt_shape S rho x (s - 1)).2.2.symm.trans hconfirmed)
      have hDH : D = H := hexec.core.toNamedRootCollisionFree.root_injective
        D H hDrun hHrun' D H (Or.inl (Proofs.NamedAncestry.named_self D))
          (Or.inr (Proofs.NamedAncestry.named_self H)) hrootEq
      have hHErase : H.erase = actionSGBlockAt S rho x (s - 1) := by
        rw [← hDH, hDerase]
      have hcarrierHead := (hsources (s - 1)
        (hsourceTime (s - 1) (Nat.sub_lt hs (by decide)))).1 x hxHon hemitAction
      have hFread : Block.Preceq
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc s .g1) reader).st.core.F
          (voterHeadAt S rho w d) := by
        have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
          S rho (domain S.E S.hc s .g1) reader
        have hFr := Proofs.Records.preceq_get_fg_root_of_F
          (st := (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc s .g1) reader).st.core.toHealing.toFG) hFJ
        have hrootRead : Block.Preceq
            (Protocol.get_fg_root
              (NamedRun.stateBeforeTime S rho
                (domain S.E S.hc s .g1) reader).st.core.toHealing.toFG)
            (voterHeadAt S rho w d) := by
          rcases WeakFG.fgRoot_confirmationWitness_at_read
              S hexec.core hmajority hreader (domain S.E S.hc s .g1) with
            hgen | ⟨C', -, -, a', ta', ha', hemit', hat', -, hT'⟩
          · have hgen' : Protocol.get_fg_root
                (NamedRun.stateBeforeTime S rho
                  (domain S.E S.hc s .g1) reader).st.core.toHealing.toFG =
                Block.genesis := by
              simpa only [Run.storeBeforeTime] using hgen
            rw [hgen']
            exact Protocol.preceq_genesis _
          · have htime' : ta' = S.a a'.round := (emits_attest_shape S hemit').2
            apply ((hsources a'.round ?_).2 a'.val_index ha').2 _ hT'
            rw [← htime']
            have hdomainVote : domain S.E S.hc s .g1 ≤
                Protocol.vote_time S.E (d + 1) := by
              rw [NamedOutageClosure.domain_g1_eq_opening,
                DecoupledConsensusModel.Protocol.opening, ← Protocol.Γ_0_eq_proposal_time]
              exact (Protocol.proposal_time_lt_vote_time S.E d).le.trans
                (Protocol.vote_time_mono_slots S.E (Nat.le_succ d))
            exact hat'.trans_le hdomainVote
        exact Block.preceq_trans (by simpa only [Protocol.Store.toHealing] using hFr) hrootRead
      have hdeadlineG2 : S.a (s - 1) + S.E.Δ ≤ early S.E S.hc s .g2 :=
        NamedOutageClosure.action_delta_le_early S (q := s - 1) (r := s)
          S.hc.R_ge_three (Nat.sub_lt hs (by decide))
      have hdeadline : S.a (s - 1) + S.E.Δ ≤ early S.E S.hc s .g1 := by
        apply hdeadlineG2.trans
        simp only [early, Phase.earlyOffset]
        linarith [S.E.Δ_pos]
      have hearlyDomain : early S.E S.hc s .g1 ≤ domain S.E S.hc s .g1 := by
        simp only [early, domain, Phase.earlyOffset, Phase.domainOffset]
        linarith [S.E.Δ_pos]
      obtain ⟨y, hy, hyr, hyc, hyfind⟩ :=
        interpretedInputs_nonempty_of_honest_window_vote_of_delivery_common_upper
          S hexec.core .g1 hexec.healthy
          (NamedOutageClosure.mem_latest_window
            (Nat.sub_le_sub_left S.hc.η_SG_ge_one s)
            (Nat.sub_lt hs (by decide))) hxHon hreader
          (hvote := ⟨(actionAttestationAt_shape S rho x (s - 1)).1,
            (actionAttestationAt_shape S rho x (s - 1)).2.1, hemitAction⟩)
          (hhead := ⟨i, hi, hH, hconfirmed⟩)
          (C := voterHeadAt S rho w d)
          (by rw [hHErase]; exact hcarrierHead) hFread
          (by simpa only [actionAttestationAt_shape] using hdeadline)
          hearlyDomain (hearlyDomain.trans
            ((FrameForward.domain_le_a S s .g1).trans hasCap))
      refine ⟨y, hy, ?_, ?_, ?_⟩
      · exact hyr
      · simpa only [hHErase] using hyc
      · have hHroot : H.root = (actionSGBlockAt S rho x (s - 1)).root := by
          rw [← Proofs.NamedWire.erase_root H, hHErase]
        rw [hHroot, hHErase] at hyfind
        exact hyfind
    have hcarrier := relativeGradeCarrierAt_of_gradeFormingMajority
      S hexec.core hs hwindow
        (hforming s hs (Or.inl ⟨Proofs.HealingLemmas.a_nonneg S s,
          hasCap.trans hcapHor⟩)) u hu raw hgrade
    obtain ⟨k, hk, x, hx, hemit, hrawCarrier⟩ := hcarrier
    have hklt : k < s := mem_latestWindow_lt hk
    have hcarrierHead := (hsources k (hsourceTime k hklt)).1 x hx hemit
    have hAraw : Block.Preceq A raw := by
      unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
      exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
    exact Block.preceq_trans hAraw
      (Block.preceq_trans hrawCarrier hcarrierHead)

#print axioms openingHeads_above_confirmationAnchors

/-- The stable-seeded name, kept for the existing callers: the seed is unused. -/
theorem stableAt_openingHeads_above_confirmationAnchors
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s : Round) (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (_hslash : NamedOutageEntry.SlashableBound S rho)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (_hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (_hstable : stableAt S rho v s P) (hs : 0 < s) :
    ∀ u ∈ rho.honest, ∀ w ∈ rho.honest,
      Block.Preceq
        (confirmationAnchorAt S rho u (S.hc.opening_slot s))
        (voterHeadAt S rho w (S.hc.opening_slot s)) :=
  openingHeads_above_confirmationAnchors S rho b0 b1 s hexec hcom hsleep hforming hmargin hs

private theorem canonicalSuffixHonestVoteCounted_of_delivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : HonestDeliveryBefore S rho cap)
    {s : Slot} (hs : 0 < s) (hcap : Protocol.confirmation_time S.E s ≤ cap)
    (v : V) (hv : v ∈ rho.honest)
    (vote : GoldfishVote V) (hslot : vote.slot = s)
    (hhon : vote.val_index ∈ rho.honest)
    (hemit : rho.emits S vote.val_index (.gfVote vote)
      (Protocol.vote_time S.E s))
    (harr : HeadArrivesBefore
      (confStore S rho v s).T (confStore S rho v s).timestamp_block
      (Protocol.support_cutoff S.E s) vote) :
    vote ∈ confVotes S.E (confStore S rho v s) s := by
  have hle : Protocol.support_cutoff S.E s ≤
      Protocol.confirmation_time S.E s := support_cutoff_le_confirmation_time S.E s
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed (Protocol.confirmation_time S.E s)
  have hstore : rho.storeBeforeTime S v (Protocol.confirmation_time S.E s) =
      (rho.stateBefore S n v).st :=
    congrArg NamedNodeState.st (congrFun hn v)
  obtain ⟨H, hfind, hstamp⟩ := harr
  have hrecv : vote ∈ beforeCutoff
      (confStore S rho v s).timestamp_vote
      (Protocol.support_cutoff S.E s) ((confStore S rho v s).pool s) :=
      gfVote_in_cutoff_view_of_delivery S adm hdelivery hhon hs hemit hslot hv
      _ _ hle (le_refl _) (hle.trans hcap)
  have hHmem : H ∈
      (rho.storeBeforeTime S v (Protocol.confirmation_time S.E s)).T := by
    simpa only [confStore, tickStore] using
      (Proofs.HealingLemmas.find?_mem hfind)
  have hHslot : H.slot ≤ vote.slot :=
    Proofs.Optimistic.emitted_vote_head_slot_le_of_store_mem S adm hhon hv hemit hslot
      hHmem (Proofs.HealingLemmas.find?_root hfind)
  have hearly : vote ∈ confEarly S.E (confStore S rho v s) s :=
    mem_tau_cutoff_of hrecv hfind hHslot hstamp
  rw [confVotes, Finset.mem_filter]
  refine ⟨hearly, ?_⟩
  simp only [Protocol.no_second_vote_in, decide_eq_true_eq]
  intro x hx
  by_cases hxv : x.val_index = vote.val_index
  · refine Or.inl ?_
    have hxpool : x ∈ (rho.stateBefore S n v).st.gf_votes s := by
      have h := (Finset.mem_filter.mp hx).1
      rw [confStore, Protocol.Store.pool, List.mem_toFinset] at h
      rw [← hstore]
      exact h
    have hvpool : vote ∈ (rho.stateBefore S n v).st.gf_votes s := by
      have h := (Finset.mem_filter.mp hearly).1
      rw [confStore, Protocol.Store.pool, List.mem_toFinset] at h
      rw [← hstore]
      exact h
    have hps := poolStamps_stateBefore S adm.toNamedScheduleWellFormed v n
    exact named_voteVisible_unique S adm v n
      (Or.inl ⟨s, hxpool⟩) (Or.inl ⟨s, hvpool⟩)
      (by rw [hxv]; exact hhon) hxv.symm
      (by rw [hps.slot s x hxpool, hps.slot s vote hvpool])
  · exact Or.inr hxv

set_option maxHeartbeats 400000 in
/-- Every honest opening confirmation is genuine and extends its own prepared
anchor. -/
theorem openingConfirmation_genuine_above_anchor
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (s : Round)
    (hexec : OutageExecution S rho b0 b1)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hmargin : FormationMargin S s b0) (hs : 0 < s) :
    ∀ u ∈ rho.honest,
      let slot := S.hc.opening_slot s
      let read := Internal.NamedRecoveryRead.confirmationInputRead S rho u slot
      let contract := NamedProfile.gradeContract read.cache
      let output := (Protocol.update_confirmation_with contract S.E S.hc
        (confStore S rho u slot) slot).live_confirmed
      GenuineConfirmationWith contract S.E S.hc
          (confStore S rho u slot) slot output ∧
        Block.Preceq (confirmationAnchorAt S rho u slot) output := by
  have hcap : b0 ≤ rho.horizon := hexec.interval.2.1.trans hexec.interval.2.2
  have hasCap : S.a s ≤ b0 :=
    (Assembly.a_mono S (Nat.le_succ s)).trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin)
  have hheads := openingHeads_above_confirmationAnchors
    S rho b0 b1 s hexec hcom hsleep hforming hmargin hs
  intro u hu
  dsimp only
  let slot := S.hc.opening_slot s
  let read := Internal.NamedRecoveryRead.confirmationInputRead S rho u slot
  let st := confStore S rho u slot
  let contract := NamedProfile.gradeContract read.cache
  let A := confirmationAnchorAt S rho u slot
  have hslotPos : 0 < slot := by
    dsimp only [slot, Protocol.HealConfig.opening_slot]
    exact Nat.mul_pos hs (Nat.zero_lt_of_lt S.hc.R_ge_two)
  have hvoteHor : Protocol.vote_time S.E slot ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E slot).trans
      (by simpa only [slot, opening_confirmation_time_eq_action] using hasCap.trans hcap)
  have hsupport : ConeSupport S.E st.T
      (confVotes S.E st slot) (confVotes S.E st slot)
      (confLate S.E st slot) slot rho.honest
      (fun X => Block.Preceq A X) := by
    have hN := confNumerator S.E st slot
    refine coneSupport_of_named_votes (hcom slot) hN.subset_late
      (subset_refl _) (fun y _ _ => hN.no_equivocation y) ?_
    intro x hxCommittee hxHon
    obtain ⟨X, hXerase, hXrun, hXemit⟩ :=
      WeakGoldfish.voterHead_runBlock_and_emits
        S hexec.core hxHon hslotPos hxCommittee hvoteHor
    have hheadMem : voterHeadAt S rho x slot ∈
        (Internal.NamedRecoveryRead.voteDutyRead S rho x slot).st.core.T := by
      let duty := Internal.NamedRecoveryRead.voteDutyRead S rho x slot
      have hinvPre : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
          (rho.stateBeforeTime S (Protocol.vote_time S.E slot) x).st :=
        (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
          (Protocol.vote_time S.E slot) x).1
      have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg duty.st := by
        simpa only [duty, Internal.NamedRecoveryRead.voteDutyRead,
          NamedActionReads.confirmationReadAt] using
          Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ _ hinvPre
      have hroot : Protocol.get_fg_root duty.st.core.toHealing.toFG ∈
          duty.st.core.T := Proofs.NamedStoreRoots.fg_root_mem duty.st hinv.1.2
      have hanchor : voterAnchorAt S rho x slot ∈ duty.st.core.T :=
        Proofs.NamedConfirmationMembership.runtime_anchor_mem duty.cache
          S.E S.hc duty.st.core.toHealing
          (S.hc.round_of duty.st.core.s) hroot
      have htree : voterCandidateTreeAt S rho x slot ⊆ duty.st.core.T := by
        intro D hD
        exact (Finset.mem_filter.mp
          (Proofs.Records.get_filtered_block_tree_from_subset
            duty.st.core.toHealing.toFG
            (Protocol.voter_processed_block_tree S.E
              duty.st.core.toHealing.toFG.toSG.toGoldfishStore duty.st.core.s) hD)).1
      exact Proofs.Records.ghost_mem_of _ _ hanchor htree
    have hXbody : X ∈ (NamedRun.stateBeforeTime S rho
        (Protocol.vote_time S.E slot) x).st.bodies := by
      have hcore : X.erase ∈ (NamedRun.stateBeforeTime S rho
          (Protocol.vote_time S.E slot) x).st.core.T := by
        simpa only [Internal.NamedRecoveryRead.voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock, hXerase] using hheadMem
      have htree := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
        (Protocol.vote_time S.E slot) x).1.1.1.1
      rw [htree] at hcore
      obtain ⟨Y, hY, hYerase⟩ := Finset.mem_image.mp hcore
      obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
        S rho hexec.core.sorted (Protocol.vote_time S.E slot)
      have hYprefix : Y ∈ (NamedRun.stateBefore S rho n x).st.bodies := by
        rw [← hn]
        exact hY
      have hYrun : RunBlock S rho Y :=
        Proofs.Bridges.runBlock_of_stateBefore_mem S hxHon hYprefix
      have hYX : Y = X := hexec.core.toNamedRootCollisionFree.root_injective
        Y X hYrun hXrun Y X (Or.inl (Proofs.NamedAncestry.named_self Y))
          (Or.inr (Proofs.NamedAncestry.named_self X)) (by
            rw [← Proofs.NamedWire.erase_root Y, ← Proofs.NamedWire.erase_root X,
              hYerase, hXerase])
      simpa only [hYX] using hY
    have hF : Block.Preceq
        (NamedRun.stateBeforeTime S rho
          (Protocol.confirmation_time S.E slot) u).st.core.F X.erase := by
      have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        S rho (Protocol.confirmation_time S.E slot) u
      have hFroot := Proofs.Records.preceq_get_fg_root_of_F
        (st := (NamedRun.stateBeforeTime S rho
          (Protocol.confirmation_time S.E slot) u).st.core.toHealing.toFG) hFJ
      have hrootA : Block.Preceq
          (Protocol.get_fg_root
            (NamedRun.stateBeforeTime S rho
              (Protocol.confirmation_time S.E slot) u).st.core.toHealing.toFG) A := by
        have h := fg_root_preceq_get_sg_root_with_frame read.cache S.E S.hc
          read.st.core.toHealing (S.hc.round_of read.st.core.s)
        simpa only [A, confirmationAnchorAt, namedConfirmationAnchor, read,
          Internal.NamedRecoveryRead.confirmationInputRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock] using h
      exact Block.preceq_trans (by simpa only [Protocol.Store.toHealing] using hFroot)
        (Block.preceq_trans hrootA (by
          rw [hXerase]
          exact hheads u hu x hxHon))
    obtain ⟨-, hstamp, hfind⟩ := NamedHealthyHeadReady.healthy_head_body_at_read
      S rho hexec.core b0 hexec.healthy x hxHon u hu X
      (Protocol.vote_time S.E slot) (Protocol.support_cutoff S.E slot)
      (Protocol.confirmation_time S.E slot) hXbody
      (by rw [Proofs.Optimistic.vote_time_add_delta])
      (support_cutoff_le_confirmation_time S.E slot)
      ((support_cutoff_le_confirmation_time S.E slot).trans
        (by simpa only [slot, opening_confirmation_time_eq_action] using hasCap)) hF
    have hcount : (⟨x, slot, X.erase.root⟩ : GoldfishVote V) ∈
        confVotes S.E st slot := by
      apply canonicalSuffixHonestVoteCounted_of_delivery
        S hexec.core hexec.healthy hslotPos
          (by simpa only [slot, opening_confirmation_time_eq_action] using hasCap)
          u hu _ rfl hxHon hXemit
      exact ⟨X.erase, by simpa only [st, confStore, tickStore] using hfind,
        by simpa only [st, confStore, tickStore] using hstamp⟩
    have hXmem : X.erase ∈
        (NamedRun.stateBeforeTime S rho
          (Protocol.confirmation_time S.E slot) u).st.core.T := by
      exact Proofs.HealingLemmas.find?_mem hfind
    have hXslot : X.erase.slot ≤ slot :=
      Proofs.Optimistic.emitted_vote_head_slot_le_of_store_mem S hexec.core hxHon hu hXemit rfl
        hXmem (by rfl)
    exact ⟨X.erase, by rw [hXerase]; exact hheads u hu x hxHon,
      hXslot, hcount, by simpa only [st, confStore, tickStore] using hfind⟩
  have hvalid : Protocol.VoteSetValid S.E slot (confLate S.E st slot) := by
    simpa only [st, confStore, tickStore] using
      voteSetValid_confLate_stateBeforeTime S
        hexec.core.toNamedScheduleWellFormed u
          (Protocol.confirmation_time S.E slot) slot
  have hAeligible : confEligible S.E st slot A = true := by
    simp only [confEligible, decide_eq_true_eq, confCount, confScore]
    exact hsupport.eligible hvalid (fun _ h => h)
  have hwalkEligible : confEligible S.E st slot
      (confWalkWith contract S.E S.hc st slot) = true := by
    rcases ghost_eligible (confAnchorWith contract S.E S.hc st)
        (confTree st) (confScore S.E st slot) (confEligible S.E st slot) with
      hwalk | helig
    · have hanchor : confAnchorWith contract S.E S.hc st = A := by
        rfl
      rw [show confWalkWith contract S.E S.hc st slot = A by
        simpa only [confWalkWith, hanchor] using hwalk]
      exact hAeligible
    · exact helig
  have hfloor : Block.Preceq A
      (confWalkWith contract S.E S.hc st slot) := by
    change Block.Preceq (confAnchorWith contract S.E S.hc st)
      (confWalkWith contract S.E S.hc st slot)
    simpa only [confWalkWith] using ghost_preceq
      (confAnchorWith contract S.E S.hc st) (confTree st)
        (confScore S.E st slot) (confEligible S.E st slot)
  refine ⟨⟨rfl, hwalkEligible⟩, ?_⟩
  rw [update_confirmation_with_live_confirmed, if_pos hwalkEligible]
  exact hfloor

#print axioms openingConfirmation_genuine_above_anchor

/-- The stable-seeded name, kept for the existing callers: the seed is unused. -/
theorem stableAt_openingConfirmation_genuine_above_anchor
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s : Round) (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (_hslash : NamedOutageEntry.SlashableBound S rho)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (_hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (_hstable : stableAt S rho v s P) (hs : 0 < s) :
    ∀ u ∈ rho.honest,
      let slot := S.hc.opening_slot s
      let read := Internal.NamedRecoveryRead.confirmationInputRead S rho u slot
      let contract := NamedProfile.gradeContract read.cache
      let output := (Protocol.update_confirmation_with contract S.E S.hc
        (confStore S rho u slot) slot).live_confirmed
      GenuineConfirmationWith contract S.E S.hc
          (confStore S rho u slot) slot output ∧
        Block.Preceq (confirmationAnchorAt S rho u slot) output :=
  openingConfirmation_genuine_above_anchor S rho b0 b1 s hexec hcom hsleep hforming hmargin hs

set_option maxHeartbeats 400000 in
private theorem phaseGrade_preceq_openingHead
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (s : Round) (hexec : OutageExecution S rho b0 b1)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hmargin : FormationMargin S s b0) (hs : 0 < s)
    (p : Phase) {u w : V} (hu : u ∈ rho.honest) (hw : w ∈ rho.honest)
    {B : Block V}
    (hgrade : storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc s p) u).st s p B = true) :
    Block.Preceq B (voterHeadAt S rho w (S.hc.opening_slot s)) := by
  have hcapHor : b0 ≤ rho.horizon :=
    hexec.interval.2.1.trans hexec.interval.2.2
  have hasCap : S.a s ≤ b0 :=
    (Assembly.a_mono S (Nat.le_succ s)).trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin)
  have hroundOne : domain S.E S.hc 1 .g2 ≤ b0 := by
    exact (FrameForward.domain_le_a S 1 .g2).trans
      ((Assembly.a_mono S (Nat.succ_le_succ (Nat.zero_le s))).trans
        ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin))
  have hT1 := protectedVoteSlots_before
    S rho b0 b1 hexec hcom hsleep hroundOne
  let d := S.hc.opening_slot s
  have hd : 1 ≤ d := by
    dsimp only [d, Protocol.HealConfig.opening_slot]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hs.ne'
      (Nat.ne_of_gt (Nat.zero_lt_of_lt S.hc.R_ge_two)))
  have hdCap : Protocol.vote_time S.E d + S.E.Δ ≤ b0 := by
    rw [Proofs.Optimistic.vote_time_add_delta]
    exact (Protocol.support_cutoff_le_confirmation_time S.E d).trans
      (by simpa only [d, Proofs.HealingSurface.opening_confirmation_time_eq_action]
        using hasCap)
  have hsources := actionSources_preceq_voteDutyHead_before_of_T1
    S rho b0 b1 hexec hcom hsleep hroundOne hT1 hd hdCap hw
  have hsourceTime : ∀ k, k < s →
      S.a k < Protocol.vote_time S.E (d + 1) := by
    intro k hk
    exact (Int.lt_add_of_pos_right _ S.E.Δ_pos).trans_le
      ((Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt S hk).trans
        ((Protocol.proposal_time_lt_vote_time S.E d).le.trans
          (Protocol.vote_time_mono_slots S.E (Nat.le_succ d))))
  have hmajority : HonestWeightMajority S rho.honest := by
    apply WeakSG.honestWeightMajority_of_awakeWindowMajority S
    exact hsleep s hs (Or.inl ⟨Proofs.HealingLemmas.a_nonneg S s,
      hasCap.trans hcapHor⟩)
  have hwindow : RelativeCarrierWindowAt S rho (s - 1) p := by
    intro reader hreader x hx
    change ∃ y ∈ interpretedInputs
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc ((s - 1) + 1) p) reader).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc ((s - 1) + 1) p) reader).st.core.F
        S.hc.η_SG ((s - 1) + 1) (early S.E S.hc ((s - 1) + 1) p) x,
      y.round = s - 1 ∧
      y.confirmed = some (actionSGBlockAt S rho x (s - 1)).root ∧
      Block.find?
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc ((s - 1) + 1) p) reader).st.core.T
        (actionSGBlockAt S rho x (s - 1)).root =
          some (actionSGBlockAt S rho x (s - 1))
    simp only [Nat.sub_add_cancel hs]
    obtain ⟨hxHon, a, hax, haround, hemit⟩ :=
      (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho x (s - 1)).mp hx
    have hxAwake : (S.node x).awake (s - 1) = true := by
      simpa only [haround] using emits_attest_awake S hemit
    have hactionHor : S.a (s - 1) ≤ rho.horizon :=
      (Assembly.a_mono S (Nat.sub_le s 1)).trans (hasCap.trans hcapHor)
    have hemitAction := honest_emits_exact_actionAttestationAt_of_awake
      S hexec.core.toNamedScheduleWellFormed hxHon (s - 1) hxAwake hactionHor
    obtain ⟨i, hi, -, hbody⟩ :=
      Proofs.NamedOutageInputs.emitted_attestation_head S rho hemitAction
    dsimp at hbody
    obtain ⟨H, hH, hconfirmed⟩ := hbody
    have hstate := NamedActionSources.action_read_index S rho
      hexec.core.toNamedScheduleWellFormed i x (s - 1) hi
    have hHsource : H ∈
        (NamedRun.stateBeforeTime S rho (S.a (s - 1)) x).st.bodies := by
      rw [← hstate]
      exact hH
    have hcarrierMem : actionSGBlockAt S rho x (s - 1) ∈
        (NamedRun.stateBeforeTime S rho (S.a (s - 1)) x).st.core.T :=
      actionSGBlockAt_mem_storeBeforeTime S rho x (s - 1)
    obtain ⟨D, hDbody, hDerase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
        (S.a (s - 1)) x hcarrierMem
    obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
      S rho hexec.core.sorted (S.a (s - 1))
    have hDprefix : D ∈ (NamedRun.stateBefore S rho n x).st.bodies := by
      rw [← hn]
      exact hDbody
    have hHprefix : H ∈ (NamedRun.stateBefore S rho n x).st.bodies := by
      rw [← hn]
      exact hHsource
    have hDrun : RunBlock S rho D :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S hxHon hDprefix
    have hHrun : RunBlock S rho H :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S hxHon hHprefix
    have hrootEq : D.root = H.root := by
      rw [← Proofs.NamedWire.erase_root D, hDerase]
      exact Option.some.inj
        ((actionAttestationAt_shape S rho x (s - 1)).2.2.symm.trans hconfirmed)
    have hDH : D = H := hexec.core.toNamedRootCollisionFree.root_injective
      D H hDrun hHrun D H (Or.inl (Proofs.NamedAncestry.named_self D))
        (Or.inr (Proofs.NamedAncestry.named_self H)) hrootEq
    have hHErase : H.erase = actionSGBlockAt S rho x (s - 1) := by
      rw [← hDH, hDerase]
    have hcarrierHead :=
      (hsources (s - 1) (hsourceTime (s - 1)
        (Nat.sub_lt hs (by decide)))).1 x hxHon hemitAction
    have hFread : Block.Preceq
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc s p) reader).st.core.F
        (voterHeadAt S rho w d) := by
      have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        S rho (domain S.E S.hc s p) reader
      have hFr := Proofs.Records.preceq_get_fg_root_of_F
        (st := (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc s p) reader).st.core.toHealing.toFG) hFJ
      have hrootRead : Block.Preceq
          (Protocol.get_fg_root
            (NamedRun.stateBeforeTime S rho
              (domain S.E S.hc s p) reader).st.core.toHealing.toFG)
          (voterHeadAt S rho w d) := by
        rcases WeakFG.fgRoot_confirmationWitness_at_read
            S hexec.core hmajority hreader (domain S.E S.hc s p) with
          hgen | ⟨C, -, -, a', ta', ha', hemit', hat', -, hT'⟩
        · have hgen' : Protocol.get_fg_root
              (NamedRun.stateBeforeTime S rho
                (domain S.E S.hc s p) reader).st.core.toHealing.toFG =
              Block.genesis := by
            simpa only [Run.storeBeforeTime] using hgen
          rw [hgen']
          exact Protocol.preceq_genesis _
        · have htime' : ta' = S.a a'.round := (emits_attest_shape S hemit').2
          apply ((hsources a'.round ?_).2 a'.val_index ha').2 _ hT'
          rw [← htime']
          have hdomainVote : domain S.E S.hc s p ≤
              Protocol.vote_time S.E (d + 1) := by
            apply (show domain S.E S.hc s p ≤ domain S.E S.hc s .g0 by
              cases p <;>
                simp only [domain, Phase.domainOffset] <;>
                linarith [S.E.Δ_pos]).trans
            rw [Proofs.HealingSurface.domain_g0_eq_Γ_1,
              Protocol.Γ_1_eq_vote_time]
            exact Protocol.vote_time_mono_slots S.E (Nat.le_succ d)
          exact hat'.trans_le hdomainVote
      exact Block.preceq_trans
        (by simpa only [Protocol.Store.toHealing] using hFr) hrootRead
    have hdeadlineG2 : S.a (s - 1) + S.E.Δ ≤ early S.E S.hc s .g2 :=
      action_delta_le_early S (q := s - 1) (r := s)
        S.hc.R_ge_three (Nat.sub_lt hs (by decide))
    have hdeadline : S.a (s - 1) + S.E.Δ ≤ early S.E S.hc s p := by
      apply hdeadlineG2.trans
      cases p <;>
        simp only [early, Phase.earlyOffset] <;>
        linarith [S.E.Δ_pos]
    have hearlyDomain : early S.E S.hc s p ≤ domain S.E S.hc s p := by
      cases p <;>
        simp only [early, domain, Phase.earlyOffset, Phase.domainOffset] <;>
        linarith [S.E.Δ_pos]
    obtain ⟨y, hy, hyr, hyc, hyfind⟩ :=
      interpretedInputs_nonempty_of_honest_window_vote_of_delivery_common_upper
        S hexec.core p hexec.healthy
        (mem_latest_window (Nat.sub_le_sub_left S.hc.η_SG_ge_one s)
          (Nat.sub_lt hs (by decide))) hxHon hreader
        (hvote := ⟨(actionAttestationAt_shape S rho x (s - 1)).1,
          (actionAttestationAt_shape S rho x (s - 1)).2.1, hemitAction⟩)
        (hhead := ⟨i, hi, hH, hconfirmed⟩)
        (C := voterHeadAt S rho w d)
        (by rw [hHErase]; exact hcarrierHead) hFread
        (by simpa only [actionAttestationAt_shape] using hdeadline)
        hearlyDomain (hearlyDomain.trans
          ((FrameForward.domain_le_a S s p).trans hasCap))
    refine ⟨y, hy, hyr, ?_, ?_⟩
    · simpa only [hHErase] using hyc
    · have hHroot : H.root = (actionSGBlockAt S rho x (s - 1)).root := by
        rw [← Proofs.NamedWire.erase_root H, hHErase]
      rw [hHroot, hHErase] at hyfind
      exact hyfind
  have hcarrier := relativeGradeCarrierAt_of_gradeFormingMajority
    S hexec.core hs hwindow
      (hforming s hs (Or.inl ⟨Proofs.HealingLemmas.a_nonneg S s,
        hasCap.trans hcapHor⟩)) u hu B hgrade
  obtain ⟨k, hk, x, hx, hemit, hBcarrier⟩ := hcarrier
  have hklt : k < s := mem_latestWindow_lt hk
  have hcarrierHead := (hsources k (hsourceTime k hklt)).1 x hx hemit
  exact Block.preceq_trans hBcarrier hcarrierHead

set_option maxHeartbeats 400000 in
/-- At the stable round, every honest prepared action frame clears its own
anchor. -/
theorem stableAt_actionAnchor_clear
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s : Round) (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : NamedOutageEntry.SlashableBound S rho)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hstable : stableAt S rho v s P) (hs : 0 < s) :
    ∀ u ∈ rho.honest,
      nodeClear S (Proofs.HealingSurface.actionReadAt S rho u s) s
        (nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho u s) s) = true := by
  have hcap : b0 ≤ rho.horizon :=
    hexec.interval.2.1.trans hexec.interval.2.2
  have hasCap : S.a s ≤ b0 :=
    (Assembly.a_mono S (Nat.le_succ s)).trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin)
  have hhor : S.a s ≤ rho.horizon := hasCap.trans hcap
  have hdomainCap : domain S.E S.hc s .g0 ≤ b0 :=
    (FrameForward.domain_le_a S s .g0).trans hasCap
  have hdomainHor : domain S.E S.hc s .g0 ≤ rho.horizon :=
    hdomainCap.trans hcap
  obtain ⟨G, raw, -, -, hG1, -⟩ :=
    stableAt_rawG2_viableDescendant_at_openingVote
      S rho b0 b1 v s P hexec hslash hcom hsleep hforming
        hv hmargin hstable hs
  intro u hu
  have hG1u : storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc s .g1) u).st s .g1 raw = true :=
    hG1 u hu
  have hrawTree : raw ∈
      (readAt S rho (domain S.E S.hc s .g1) u).st.core.T :=
    namedG1At_mem_domainTree S rho (by
      simpa only [namedG1At] using hG1u)
  obtain ⟨raw1, hraw1, -⟩ := q10_freeze_of_graded S.E
    (readAt S rho (domain S.E S.hc s .g1) u).st.core.toHealing.gradeView
    (readAt S rho (domain S.E S.hc s .g1) u).st.core.F
    S.hc.η_SG s (q10_early_le_late S s .g1) hrawTree
    (by simpa only [storeGrade] using hG1u)
  let root1 := DecoupledConsensusModel.Protocol.clipGrade raw1
    (Proofs.HealingSurface.actionReadAt S rho u s).st.core.F
  have hframe :
      (DecoupledConsensusModel.Protocol.readFrame
        (Proofs.HealingSurface.actionReadAt S rho u s).cache
        (Proofs.HealingSurface.actionReadAt S rho u s).st.core.toHealing s).g1 =
          some (some root1) := by
    have h := Proofs.HealingSurface.actionFrame_g1 S hexec.core hu hs hhor
    have hstore : storeRoot S.E S.hc
        (readAt S rho (domain S.E S.hc s .g1) u).st s .g1 = some raw1 := by
      simpa only [storeRoot, phaseRoot] using hraw1
    simpa only [hstore, Option.map_some, root1] using h
  cases hactive : DecoupledConsensusModel.Protocol.activePrefix
      (filteredTree (Proofs.HealingSurface.actionReadAt S rho u s)) root1 with
  | some A =>
      have hanchor : nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho u s) s = A := by
        simp only [nodeAnchor, nodeRead, NamedProfile.gradeContract,
          DecoupledConsensusModel.Protocol.frameContract, DecoupledConsensusModel.Protocol.frameGradeRead,
          DecoupledConsensusModel.Protocol.anchor, hframe, hactive, Option.getD_some]
      have hAactive : A ∈
          filteredTree (Proofs.HealingSurface.actionReadAt S rho u s) :=
        (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).1
      have hAG1 := activeActionAnchor_storeGrade_g1
        S hexec.core hs hhor hu hframe hactive
      have hAG0 := storeGrade_g0_of_sameReader_g1_healthyPrefix
        S hexec.core hs b0 hexec.healthy hdomainCap hdomainHor hu hAG1 hAactive
      rw [hanchor]
      exact actionRead_clear_of_domainG0Grade
        S rho hexec.core hu hs hhor hAG0 hAactive
  | none =>
      obtain ⟨w, hw⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
      have hheads := stableAt_openingHeads_above_confirmationAnchors
        S rho b0 b1 v s P hexec hslash hcom hsleep hforming
          hv hmargin hstable hs
      have hanchorHead : Block.Preceq
          (nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho u s) s)
          (voterHeadAt S rho w (S.hc.opening_slot s)) := by
        rw [actionAnchor_eq_openingConfirmationAnchor]
        exact hheads u hu w hw
      have hframe0 := actionRead_g0Root_eq_domainG0
        S rho hexec.core hu hs hhor
      unfold nodeClear nodeRead
      change DecoupledConsensusModel.Protocol.clear
        (DecoupledConsensusModel.Protocol.readFrame
          (Proofs.HealingSurface.actionReadAt S rho u s).cache
          (Proofs.HealingSurface.actionReadAt S rho u s).st.core.toHealing s)
        (nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho u s) s) = true
      unfold DecoupledConsensusModel.Protocol.clear
      rw [hframe0]
      cases hroot0 : storeRoot S.E S.hc
          (readAt S rho (domain S.E S.hc s .g0) u).st s .g0 with
      | none => rfl
      | some raw0 =>
          have hraw0Grade : storeGrade S.E S.hc
              (readAt S rho (domain S.E S.hc s .g0) u).st s .g0 raw0 = true := by
            simpa only [storeGrade, phaseGrade] using
              (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hroot0)).2
          have hraw0Head := phaseGrade_preceq_openingHead
            S rho b0 b1 s hexec hcom hsleep hforming hmargin hs
              .g0 hu hw hraw0Grade
          change Block.compatible
            (nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho u s) s)
            (DecoupledConsensusModel.Protocol.clipGrade raw0
              (Proofs.HealingSurface.actionReadAt S rho u s).st.core.F) = true
          exact Block.compatible_of_preceq_common hanchorHead
            (Block.preceq_trans (q10_clip_preceq raw0 _) hraw0Head)

#print axioms stableAt_actionAnchor_clear

set_option maxHeartbeats 400000 in
/-- Seed-free form: every honest action anchor of a pre-outage round is clear.
The active arm has a G1 grade, hence a G0 grade at the same reader; every
fallback arm is the FG root, which sits below every honest opening head, as
does the saved G0 root. -/
theorem actionAnchor_clear
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (s : Round)
    (hexec : OutageExecution S rho b0 b1)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hmargin : FormationMargin S s b0) (hs : 0 < s) :
    ∀ u ∈ rho.honest,
      nodeClear S (Proofs.HealingSurface.actionReadAt S rho u s) s
        (nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho u s) s) = true := by
  have hcap : b0 ≤ rho.horizon :=
    hexec.interval.2.1.trans hexec.interval.2.2
  have hasCap : S.a s ≤ b0 :=
    (Assembly.a_mono S (Nat.le_succ s)).trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin)
  have hhor : S.a s ≤ rho.horizon := hasCap.trans hcap
  have hdomainCap : domain S.E S.hc s .g0 ≤ b0 :=
    (FrameForward.domain_le_a S s .g0).trans hasCap
  have hdomainHor : domain S.E S.hc s .g0 ≤ rho.horizon :=
    hdomainCap.trans hcap
  intro u hu
  have hfallback :
      nodeClear S (Proofs.HealingSurface.actionReadAt S rho u s) s
        (nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho u s) s) = true := by
    obtain ⟨w, hw⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
    have hheads := openingHeads_above_confirmationAnchors
      S rho b0 b1 s hexec hcom hsleep hforming hmargin hs
    have hanchorHead : Block.Preceq
        (nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho u s) s)
        (voterHeadAt S rho w (S.hc.opening_slot s)) := by
      rw [actionAnchor_eq_openingConfirmationAnchor]
      exact hheads u hu w hw
    have hframe0 := actionRead_g0Root_eq_domainG0
      S rho hexec.core hu hs hhor
    unfold nodeClear nodeRead
    change DecoupledConsensusModel.Protocol.clear
      (DecoupledConsensusModel.Protocol.readFrame
        (Proofs.HealingSurface.actionReadAt S rho u s).cache
        (Proofs.HealingSurface.actionReadAt S rho u s).st.core.toHealing s)
      (nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho u s) s) = true
    unfold DecoupledConsensusModel.Protocol.clear
    rw [hframe0]
    cases hroot0 : storeRoot S.E S.hc
        (readAt S rho (domain S.E S.hc s .g0) u).st s .g0 with
    | none => rfl
    | some raw0 =>
        have hraw0Grade : storeGrade S.E S.hc
            (readAt S rho (domain S.E S.hc s .g0) u).st s .g0 raw0 = true := by
          simpa only [storeGrade, phaseGrade] using
            (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hroot0)).2
        have hraw0Head := phaseGrade_preceq_openingHead
          S rho b0 b1 s hexec hcom hsleep hforming hmargin hs
            .g0 hu hw hraw0Grade
        change Block.compatible
          (nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho u s) s)
          (DecoupledConsensusModel.Protocol.clipGrade raw0
            (Proofs.HealingSurface.actionReadAt S rho u s).st.core.F) = true
        exact Block.compatible_of_preceq_common hanchorHead
          (Block.preceq_trans (q10_clip_preceq raw0 _) hraw0Head)
  cases hframe : (DecoupledConsensusModel.Protocol.readFrame
      (Proofs.HealingSurface.actionReadAt S rho u s).cache
      (Proofs.HealingSurface.actionReadAt S rho u s).st.core.toHealing s).g1 with
  | none => exact hfallback
  | some g =>
    cases g with
    | none => exact hfallback
    | some root1 =>
      cases hactive : DecoupledConsensusModel.Protocol.activePrefix
          (filteredTree (Proofs.HealingSurface.actionReadAt S rho u s)) root1 with
      | some A =>
          have hanchor : nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho u s) s = A := by
            simp only [nodeAnchor, nodeRead, NamedProfile.gradeContract,
              DecoupledConsensusModel.Protocol.frameContract, DecoupledConsensusModel.Protocol.frameGradeRead,
              DecoupledConsensusModel.Protocol.anchor, hframe, hactive, Option.getD_some]
          have hAactive : A ∈
              filteredTree (Proofs.HealingSurface.actionReadAt S rho u s) :=
            (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).1
          have hAG1 := activeActionAnchor_storeGrade_g1
            S hexec.core hs hhor hu hframe hactive
          have hAG0 := storeGrade_g0_of_sameReader_g1_healthyPrefix
            S hexec.core hs b0 hexec.healthy hdomainCap hdomainHor hu hAG1 hAactive
          rw [hanchor]
          exact actionRead_clear_of_domainG0Grade
            S rho hexec.core hu hs hhor hAG0 hAactive
      | none => exact hfallback

#print axioms actionAnchor_clear

private theorem stable_chain_mem_of_preceq
    {C X : Block V} (h : Block.Preceq X C) :
    X ∈ Protocol.chain_of C := by
  induction C generalizing X with
  | genesis =>
      simp only [Block.Preceq, Block.preceq, decide_eq_true_eq] at h
      subst X
      simp [Protocol.chain_of, Protocol.chain_up, Block.depth]
  | node p s root votes support attestations proposer ih =>
      simp only [Block.Preceq, Block.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at h
      rcases h with h | h
      · subst X
        simp [Protocol.chain_of, Protocol.chain_up, Block.depth, Block.parent?]
      · have hmem : X ∈ Protocol.chain_of p := ih h
        have htail : X =
              Block.node p s root votes support attestations proposer ∨
            X ∈ Protocol.chain_up p.depth p := Or.inr hmem
        simpa [Protocol.chain_of, Protocol.chain_up, Block.depth,
          Block.parent?] using htail

private theorem actionAnchor_preceq_actionSGBlockAt_of_live_clear
    (S : Setup V) (rho : NamedRun V) (u : V) (r : Round)
    (hlive : Block.Preceq
      (nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho u r) r)
      (Proofs.HealingSurface.actionReadAt S rho u r).st.core.live_confirmed)
    (hclear : nodeClear S (Proofs.HealingSurface.actionReadAt S rho u r) r
      (nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho u r) r) = true) :
    Block.Preceq
      (nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho u r) r)
      (actionSGBlockAt S rho u r) := by
  let n := Proofs.HealingSurface.actionReadAt S rho u r
  let st := n.st.core.toHealing
  let grades := DecoupledConsensusModel.Protocol.frameGradeRead n.cache S.E S.hc st r
  have hk : S.hc.round_of st.s = r := Proofs.HealingLemmas.round_of_slotOf_a S r
  have heq : actionSGBlockAt S rho u r = Protocol.currentSGVote st grades := by
    show Protocol.get_sg_vote_with (NamedProfile.gradeContract n.cache)
        S.E S.hc st (S.hc.round_of st.s)
        (Protocol.grade2_block_with (NamedProfile.gradeContract n.cache)
          S.E S.hc st (S.hc.round_of st.s)) =
      Protocol.currentSGVote st grades
    rw [hk]
    rfl
  have hlive' : Block.Preceq grades.anchor st.live_confirmed := by
    simpa only [grades, st, n, nodeAnchor, nodeRead] using hlive
  have hclear' : grades.clear grades.anchor = true := by
    simpa only [grades, st, n, nodeClear, nodeRead] using hclear
  have hchain : grades.anchor ∈ Protocol.chain_of st.live_confirmed :=
    stable_chain_mem_of_preceq hlive'
  rw [heq]
  unfold Protocol.currentSGVote
  cases hwalk : Protocol.deepest_clear
      (some grades.anchor) st.live_confirmed grades.clear with
  | none =>
      exfalso
      have hsome := deepest_clear_isSome_of_mem
        (floor := some grades.anchor) (C := st.live_confirmed)
        (B := grades.anchor) (test := grades.clear)
        (by simpa using Block.preceq_self grades.anchor) hchain hclear'
      rw [hwalk] at hsome
      simp at hsome
  | some C =>
      have hC_live : Block.Preceq C st.live_confirmed :=
        Proofs.Engine.deepest_clear_preceq hwalk
      have hcandidate : grades.anchor ∈
          (Protocol.chain_of st.live_confirmed).toFinset.filter (fun B =>
            (some grades.anchor).elim true
                (fun anchor => Block.preceq anchor B) = true ∧
              grades.clear B = true) := by
        refine Finset.mem_filter.mpr
          ⟨List.mem_toFinset.mpr hchain, ?_, hclear'⟩
        simpa using Block.preceq_self grades.anchor
      exact Proofs.HealingLemmas.deepest?_dominates hwalk hcandidate
        (Block.compatible_of_preceq_common hlive' hC_live)

set_option maxHeartbeats 400000 in
/-- The stable raw G2 root is below every honest prepared action anchor in
the stable round. -/
theorem stableAt_raw_preceq_actionAnchor
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s : Round) (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : NamedOutageEntry.SlashableBound S rho)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hstable : stableAt S rho v s P) (hs : 0 < s) :
    ∃ G raw : Block V, Block.Preceq P G ∧ Block.Preceq G raw ∧
      ∀ u ∈ rho.honest,
        Block.Preceq raw
          (nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho u s) s) := by
  have hcap : b0 ≤ rho.horizon :=
    hexec.interval.2.1.trans hexec.interval.2.2
  have hasCap : S.a s ≤ b0 :=
    (Assembly.a_mono S (Nat.le_succ s)).trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin)
  have hhor : S.a s ≤ rho.horizon := hasCap.trans hcap
  obtain ⟨G, raw, hG, hgrade, hPG, hGraw⟩ :=
    stableAt_rawG2_grade S rho v s P hexec.core hv hs hhor hstable
  have hno : NoHonestConflictAbove S rho b0 raw :=
    stableRaw_noHonestConflictAbove_of_grade
      S rho b0 b1 s raw hexec hcom hsleep hmargin v hv hs hgrade
  have hdomainCap : domain S.E S.hc s .g0 ≤ b0 :=
    (FrameForward.domain_le_a S s .g0).trans hasCap
  have hdomainHor : domain S.E S.hc s .g0 ≤ rho.horizon :=
    hdomainCap.trans hcap
  have hdelivery : TwoCutoffDelivery S rho s :=
    twoCutoffDelivery_of_healthyPrefix S rho b0 hexec.healthy hdomainCap
  refine ⟨G, raw, hPG, hGraw, ?_⟩
  intro u hu
  have hG1 : storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc s .g1) u).st s .g1 raw = true := by
    apply storeGrade_g1_of_storeGrade_g2_cross_reader
      S rho hexec.core s hdelivery hdomainHor v u hv hu raw hgrade
    exact claimOne_guard_at_stableRound S rho b0 b1 hexec hslash hs hmargin
      hv hu hG hGraw
  have hrawTree : raw ∈
      (readAt S rho (domain S.E S.hc s .g1) u).st.core.T :=
    namedG1At_mem_domainTree S rho (by
      simpa only [namedG1At] using hG1)
  obtain ⟨Raw, hRawBody, hRawErase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (domain S.E S.hc s .g1) u hrawTree
  have hRawHeld : Raw ∈
      (NamedRun.stateBeforeTime S rho (S.a s) u).st.bodies :=
    (q10_strict_body_carry S rho hexec.core.toNamedScheduleWellFormed u
      (FrameForward.domain_le_a S s .g1) hRawBody).1
  obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
    S rho hexec.core.sorted (S.a s)
  have hRawPrefix : Raw ∈ (NamedRun.stateBefore S rho i u).st.bodies := by
    rw [← hi]
    exact hRawHeld
  have hRawRun : NamedRun.blockInRun S rho Raw :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hu hRawPrefix
  have hnoRaw : NoHonestConflictAbove S rho b0 Raw.erase := by
    simpa only [hRawErase] using hno
  obtain ⟨F, -, hFErase, hRawF⟩ :=
    NamedFinalityGuard.finalized_representative_compatible_before_boundary
      S rho b0 b1 s hexec hmargin hsleep Raw hRawRun hnoRaw
        u hu (S.a s) hasCap
  have hcompat : Block.compatible raw
      (Proofs.HealingSurface.actionReadAt S rho u s).st.core.F = true := by
    have h := Proofs.NamedWire.erase_compatible hRawF
    rw [hRawErase, hFErase] at h
    exact h
  have hframeBase := actionRead_g1Root_eq_domainG1
    S rho hexec.core hu hs hhor
  obtain ⟨raw1, hraw1, hrawRaw1⟩ := q10_freeze_of_graded S.E
    (readAt S rho (domain S.E S.hc s .g1) u).st.core.toHealing.gradeView
    (readAt S rho (domain S.E S.hc s .g1) u).st.core.F
    S.hc.η_SG s (q10_early_le_late S s .g1) hrawTree
    (by simpa only [storeGrade] using hG1)
  have hstore : storeRoot S.E S.hc
      (readAt S rho (domain S.E S.hc s .g1) u).st s .g1 = some raw1 := by
    simpa only [storeRoot, phaseRoot] using hraw1
  let root1 := DecoupledConsensusModel.Protocol.clipGrade raw1
    (Proofs.HealingSurface.actionReadAt S rho u s).st.core.F
  have hframe :
      (DecoupledConsensusModel.Protocol.readFrame
        (Proofs.HealingSurface.actionReadAt S rho u s).cache
        (Proofs.HealingSurface.actionReadAt S rho u s).st.core.toHealing s).g1 =
          some (some root1) := by
    simpa only [hstore, Option.map_some, root1] using hframeBase
  have hrawRoot1 : Block.Preceq raw root1 := by
    apply (q10_retained_prefix raw1
      (Proofs.HealingSurface.actionReadAt S rho u s).st.core.F raw hcompat).mpr
    exact hrawRaw1
  have hrootAnchor : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.HealingSurface.actionReadAt S rho u s).st.core.toHealing.toFG)
      (nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho u s) s) := by
    exact fg_root_preceq_anchor S.E S.hc
      (Proofs.HealingSurface.actionReadAt S rho u s).st.core.toHealing s
      (DecoupledConsensusModel.Protocol.readFrame
        (Proofs.HealingSurface.actionReadAt S rho u s).cache
        (Proofs.HealingSurface.actionReadAt S rho u s).st.core.toHealing s).g1
  simp only [Block.compatible, Bool.or_eq_true] at hcompat
  rcases hcompat with hrawF | hFraw
  · have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
      S rho (S.a s) u
    have hFroot : Block.Preceq
        (Proofs.HealingSurface.actionReadAt S rho u s).st.core.F
        (Protocol.get_fg_root
          (Proofs.HealingSurface.actionReadAt S rho u s).st.core.toHealing.toFG) := by
      exact Proofs.Records.preceq_get_fg_root_of_F
        (st := (Proofs.HealingSurface.actionReadAt S rho u s).st.core.toHealing.toFG)
          (by simpa only [Proofs.HealingSurface.actionReadAt,
            Internal.NamedOutageEntry.actionReadAt,
            NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
            NamedActionReads.confirmationReadFrom,
            Protocol.NamedDuties.update_confirmation_with,
            Protocol.update_confirmation_with,
            Protocol.Store.toHealing] using hFJ)
    exact Block.preceq_trans hrawF (Block.preceq_trans hFroot hrootAnchor)
  · have hV : Raw.erase ∈ Protocol.V_tree
        (NamedRun.stateBeforeTime S rho (S.a s) u).st.core.toHealing.toFG :=
      NamedFGProtection.viable_of_held_before_boundary
        S rho b0 b1 s hexec hmargin hsleep Raw hnoRaw u hu
          (S.a s) hasCap hRawHeld (by simpa only [hRawErase] using hFraw)
    have hprotected := NamedFGProtection.fg_protection_of_held_before_boundary
      S rho b0 b1 s hexec hmargin hsleep Raw hnoRaw u hu
        (S.a s) hasCap hRawHeld
    rcases hprotected with hrawRoot | hrawFiltered
    · exact Block.preceq_trans (by simpa only [hRawErase] using hrawRoot)
        hrootAnchor
    · have hrootRaw : Block.Preceq
          (Protocol.get_fg_root
            (Proofs.HealingSurface.actionReadAt S rho u s).st.core.toHealing.toFG) raw := by
        have h := Proofs.Records.preceq_get_fg_root_of_mem_filtered hrawFiltered
        simpa only [hRawErase] using h
      have hfiltered : raw ∈
          filteredTree (Proofs.HealingSurface.actionReadAt S rho u s) := by
        apply Proofs.Records.mem_filtered_of_mem_V_tree
        · simpa only [hRawErase] using hV
        · exact hrootRaw
      obtain ⟨A, hactive, hrawA⟩ :=
        activePrefix_covers hfiltered hrawRoot1
      have hanchor :
          nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho u s) s = A := by
        simp only [nodeAnchor, nodeRead, NamedProfile.gradeContract,
          DecoupledConsensusModel.Protocol.frameContract, DecoupledConsensusModel.Protocol.frameGradeRead,
          DecoupledConsensusModel.Protocol.anchor, hframe, hactive, Option.getD_some]
      rw [hanchor]
      exact hrawA

#print axioms stableAt_raw_preceq_actionAnchor

set_option maxHeartbeats 400000 in
/-- Tier 1 at the stable round: every honest action carrier extends the
stable block. -/
theorem stableAt_honestCarriersAbove_sameRound
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s : Round) (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : NamedOutageEntry.SlashableBound S rho)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hstable : stableAt S rho v s P) (hs : 0 < s) :
    HonestCarriersAbove S rho P s := by
  obtain ⟨G, raw, hPG, hGraw, hanchors⟩ :=
    stableAt_raw_preceq_actionAnchor
      S rho b0 b1 v s P hexec hslash hcom hsleep hforming
        hv hmargin hstable hs
  intro u hu
  have huHon : u ∈ rho.honest :=
    ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u s).mp hu).1
  have hPA : Block.Preceq P
      (nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho u s) s) :=
    Block.preceq_trans hPG
      (Block.preceq_trans hGraw (hanchors u huHon))
  have hconf := stableAt_openingConfirmation_genuine_above_anchor
    S rho b0 b1 v s P hexec hslash hcom hsleep hforming
      hv hmargin hstable hs u huHon
  have hAlive : Block.Preceq
      (nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho u s) s)
      (Proofs.HealingSurface.actionReadAt S rho u s).st.core.live_confirmed := by
    rw [actionAnchor_eq_openingConfirmationAnchor]
    change Block.Preceq (confirmationAnchorAt S rho u (S.hc.opening_slot s))
      (actionStoreAt S rho u s).st.core.live_confirmed
    rw [Proofs.HealingSurface.actionStoreAt_eq_update_confirmation_confStore]
    exact hconf.2
  have hclear := stableAt_actionAnchor_clear
    S rho b0 b1 v s P hexec hslash hcom hsleep hforming
      hv hmargin hstable hs u huHon
  exact Block.preceq_trans hPA
    (actionAnchor_preceq_actionSGBlockAt_of_live_clear
      S rho u s hAlive hclear)

#print axioms stableAt_honestCarriersAbove_sameRound

/-! ## Seed-free carrier floor from the opening heads (T_out) -/

omit [Fintype V] in
private theorem ancestor_body_mem' {st : Protocol.NamedStore V}
    (hpc : NamedStore.NamedParentClosed st) {A B : NamedBlock V}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
    intro hB hAB
    simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
    exact hAB ▸ hB
  | node parent s root votes support rows proposer ih =>
    intro hB hAB
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
      decide_eq_true_eq] at hAB
    rcases hAB with rfl | hparent
    · exact hB
    · exact ih (hpc.2 _ hB) hparent

set_option maxHeartbeats 400000 in
/-- Any block below every honest opening head is clear at every honest action
read of the round: the saved G0 root is also below every honest opening head. -/
theorem actionRead_clear_of_preceq_openingHeads
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s : Round)
    (hexec : OutageExecution S rho b0 b1)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hmargin : FormationMargin S s b0) (hs : 0 < s)
    (X : Block V)
    (hX : ∀ w ∈ rho.honest,
      Block.Preceq X (voterHeadAt S rho w (S.hc.opening_slot s))) :
    ∀ u ∈ rho.honest,
      nodeClear S (Proofs.HealingSurface.actionReadAt S rho u s) s X = true := by
  have hcap : b0 ≤ rho.horizon :=
    hexec.interval.2.1.trans hexec.interval.2.2
  have hasCap : S.a s ≤ b0 :=
    (Assembly.a_mono S (Nat.le_succ s)).trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin)
  have hhor : S.a s ≤ rho.horizon := hasCap.trans hcap
  intro u hu
  obtain ⟨w, hw⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  have hframe0 := actionRead_g0Root_eq_domainG0
    S rho hexec.core hu hs hhor
  unfold nodeClear nodeRead
  change DecoupledConsensusModel.Protocol.clear
    (DecoupledConsensusModel.Protocol.readFrame
      (Proofs.HealingSurface.actionReadAt S rho u s).cache
      (Proofs.HealingSurface.actionReadAt S rho u s).st.core.toHealing s) X = true
  unfold DecoupledConsensusModel.Protocol.clear
  rw [hframe0]
  cases hroot0 : storeRoot S.E S.hc
      (readAt S rho (domain S.E S.hc s .g0) u).st s .g0 with
  | none => rfl
  | some raw0 =>
      have hraw0Grade : storeGrade S.E S.hc
          (readAt S rho (domain S.E S.hc s .g0) u).st s .g0 raw0 = true := by
        simpa only [storeGrade, phaseGrade] using
          (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hroot0)).2
      have hraw0Head := phaseGrade_preceq_openingHead
        S rho b0 b1 s hexec hcom hsleep hforming hmargin hs
          .g0 hu hw hraw0Grade
      change Block.compatible X
        (DecoupledConsensusModel.Protocol.clipGrade raw0
          (Proofs.HealingSurface.actionReadAt S rho u s).st.core.F) = true
      exact Block.compatible_of_preceq_common (hX w hw)
        (Block.preceq_trans (q10_clip_preceq raw0 _) hraw0Head)

#print axioms actionRead_clear_of_preceq_openingHeads

/-- The SG vote is the deepest clear block on the confirmed chain above the
anchor: any clear block between the anchor and the confirmation is below it. -/
theorem preceq_actionSGBlockAt_of_anchor_live_clear
    (S : Setup V) (rho : NamedRun V) (u : V) (r : Round) (X : Block V)
    (hAX : Block.Preceq
      (nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho u r) r) X)
    (hlive : Block.Preceq X
      (Proofs.HealingSurface.actionReadAt S rho u r).st.core.live_confirmed)
    (hclear : nodeClear S (Proofs.HealingSurface.actionReadAt S rho u r) r X = true) :
    Block.Preceq X (actionSGBlockAt S rho u r) := by
  let n := Proofs.HealingSurface.actionReadAt S rho u r
  let st := n.st.core.toHealing
  let grades := DecoupledConsensusModel.Protocol.frameGradeRead n.cache S.E S.hc st r
  have hk : S.hc.round_of st.s = r := Proofs.HealingLemmas.round_of_slotOf_a S r
  have heq : actionSGBlockAt S rho u r = Protocol.currentSGVote st grades := by
    show Protocol.get_sg_vote_with (NamedProfile.gradeContract n.cache)
        S.E S.hc st (S.hc.round_of st.s)
        (Protocol.grade2_block_with (NamedProfile.gradeContract n.cache)
          S.E S.hc st (S.hc.round_of st.s)) =
      Protocol.currentSGVote st grades
    rw [hk]
    rfl
  have hAX' : Block.Preceq grades.anchor X := by
    simpa only [grades, st, n, nodeAnchor, nodeRead] using hAX
  have hlive' : Block.Preceq X st.live_confirmed := by
    simpa only [st, n] using hlive
  have hclear' : grades.clear X = true := by
    simpa only [grades, st, n, nodeClear, nodeRead] using hclear
  have hchain : X ∈ Protocol.chain_of st.live_confirmed :=
    stable_chain_mem_of_preceq hlive'
  rw [heq]
  unfold Protocol.currentSGVote
  cases hwalk : Protocol.deepest_clear
      (some grades.anchor) st.live_confirmed grades.clear with
  | none =>
      exfalso
      have hsome := deepest_clear_isSome_of_mem
        (floor := some grades.anchor) (C := st.live_confirmed)
        (B := X) (test := grades.clear)
        (by simpa using hAX') hchain hclear'
      rw [hwalk] at hsome
      simp at hsome
  | some C =>
      have hC_live : Block.Preceq C st.live_confirmed :=
        Proofs.Engine.deepest_clear_preceq hwalk
      have hcandidate : X ∈
          (Protocol.chain_of st.live_confirmed).toFinset.filter (fun B =>
            (some grades.anchor).elim true
                (fun anchor => Block.preceq anchor B) = true ∧
              grades.clear B = true) := by
        refine Finset.mem_filter.mpr
          ⟨List.mem_toFinset.mpr hchain, ?_, hclear'⟩
        simpa using hAX'
      exact Proofs.HealingLemmas.deepest?_dominates hwalk hcandidate
        (Block.compatible_of_preceq_common hlive' hC_live)

#print axioms preceq_actionSGBlockAt_of_anchor_live_clear

set_option maxHeartbeats 800000 in
/-- A block held below every honest opening head, with no honest conflict
above it, is below every honest opening confirmation of the round: either it
is below the prepared anchor, or the ghost walk from the anchor passes it
because every honest committee vote supports it. -/
theorem openingConfirmation_above_of_preceq_openingHeads
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s : Round)
    (hexec : OutageExecution S rho b0 b1)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hmargin : FormationMargin S s b0) (hs : 0 < s)
    (P : Block V) (hno : NoHonestConflictAbove S rho b0 P)
    (hPheads : ∀ w ∈ rho.honest,
      Block.Preceq P (voterHeadAt S rho w (S.hc.opening_slot s))) :
    ∀ u ∈ rho.honest,
      let slot := S.hc.opening_slot s
      let read := Internal.NamedRecoveryRead.confirmationInputRead S rho u slot
      let contract := NamedProfile.gradeContract read.cache
      Block.Preceq P (Protocol.update_confirmation_with contract S.E S.hc
        (confStore S rho u slot) slot).live_confirmed := by
  have hcap : b0 ≤ rho.horizon := hexec.interval.2.1.trans hexec.interval.2.2
  have hasCap : S.a s ≤ b0 :=
    (Assembly.a_mono S (Nat.le_succ s)).trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin)
  have hheads := openingHeads_above_confirmationAnchors
    S rho b0 b1 s hexec hcom hsleep hforming hmargin hs
  have hgenuine := openingConfirmation_genuine_above_anchor
    S rho b0 b1 s hexec hcom hsleep hforming hmargin hs
  intro u hu
  dsimp only
  let slot := S.hc.opening_slot s
  let read := Internal.NamedRecoveryRead.confirmationInputRead S rho u slot
  let st := confStore S rho u slot
  let contract := NamedProfile.gradeContract read.cache
  let A := confirmationAnchorAt S rho u slot
  have hAout : Block.Preceq A
      (Protocol.update_confirmation_with contract S.E S.hc st slot).live_confirmed :=
    (hgenuine u hu).2
  have hcompat := Block.compatible_of_preceq_common (hheads u hu u hu) (hPheads u hu)
  rcases (show Block.Preceq A P ∨ Block.Preceq P A by
      simpa only [Block.compatible, Bool.or_eq_true] using hcompat) with hAP | hPA
  swap
  · exact Block.preceq_trans hPA hAout
  have hslotPos : 0 < slot := by
    dsimp only [slot, Protocol.HealConfig.opening_slot]
    exact Nat.mul_pos hs (Nat.zero_lt_of_lt S.hc.R_ge_two)
  have hconfCap : Protocol.confirmation_time S.E slot ≤ b0 := by
    simpa only [slot, opening_confirmation_time_eq_action] using hasCap
  have hvoteHor : Protocol.vote_time S.E slot ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E slot).trans (hconfCap.trans hcap)
  -- `u` holds its own opening head, hence a named copy of `P` below it
  have hheadMem : voterHeadAt S rho u slot ∈
      (Internal.NamedRecoveryRead.voteDutyRead S rho u slot).st.core.T := by
    let duty := Internal.NamedRecoveryRead.voteDutyRead S rho u slot
    have hinvPre : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
        (rho.stateBeforeTime S (Protocol.vote_time S.E slot) u).st :=
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
        (Protocol.vote_time S.E slot) u).1
    have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg duty.st := by
      simpa only [duty, Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt] using
        Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ _ hinvPre
    have hroot : Protocol.get_fg_root duty.st.core.toHealing.toFG ∈
        duty.st.core.T := Proofs.NamedStoreRoots.fg_root_mem duty.st hinv.1.2
    have hanchor : voterAnchorAt S rho u slot ∈ duty.st.core.T :=
      Proofs.NamedConfirmationMembership.runtime_anchor_mem duty.cache
        S.E S.hc duty.st.core.toHealing
        (S.hc.round_of duty.st.core.s) hroot
    have htree : voterCandidateTreeAt S rho u slot ⊆ duty.st.core.T := by
      intro D hD
      exact (Finset.mem_filter.mp
        (Proofs.Records.get_filtered_block_tree_from_subset
          duty.st.core.toHealing.toFG
          (Protocol.voter_processed_block_tree S.E
            duty.st.core.toHealing.toFG.toSG.toGoldfishStore duty.st.core.s) hD)).1
    exact Proofs.Records.ghost_mem_of _ _ hanchor htree
  have hcore : voterHeadAt S rho u slot ∈ (NamedRun.stateBeforeTime S rho
      (Protocol.vote_time S.E slot) u).st.core.T := by
    simpa only [Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hheadMem
  have hcohVote : Proofs.NamedStore.Coherent S.E S.cfg
      (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E slot) u).st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (Protocol.vote_time S.E slot) u).1.1.1
  rw [hcohVote.1] at hcore
  obtain ⟨Y, hY, hYerase⟩ := Finset.mem_image.mp hcore
  obtain ⟨Pn, hPnY, hPnErase⟩ :=
    NamedOutageHistory.ReadyHeadReturn.named_ancestor_of_erase P Y
      (by rw [hYerase]; exact hPheads u hu)
  have hPnVote : Pn ∈ (NamedRun.stateBeforeTime S rho
      (Protocol.vote_time S.E slot) u).st.bodies :=
    ancestor_body_mem' hcohVote.2.2.1 hY hPnY
  have hPnHeld : Pn ∈ (NamedRun.stateBeforeTime S rho
      (Protocol.confirmation_time S.E slot) u).st.bodies :=
    (q10_strict_body_carry S rho hexec.core.toNamedScheduleWellFormed u
      (vote_time_le_confirmation_time S.E slot) hPnVote).1
  have hnoPn : NoHonestConflictAbove S rho b0 Pn.erase := by
    rw [hPnErase]; exact hno
  have hprot := NamedFGProtection.fg_protection_of_held_before_boundary
    S rho b0 b1 s hexec hmargin hsleep Pn hnoPn u hu
      (Protocol.confirmation_time S.E slot) hconfCap hPnHeld
  rw [hPnErase] at hprot
  have hrootA : Block.Preceq
      (Protocol.get_fg_root
        (NamedRun.stateBeforeTime S rho
          (Protocol.confirmation_time S.E slot) u).st.core.toHealing.toFG) A := by
    have h := fg_root_preceq_get_sg_root_with_frame read.cache S.E S.hc
      read.st.core.toHealing (S.hc.round_of read.st.core.s)
    simpa only [A, confirmationAnchorAt, namedConfirmationAnchor, read,
      Internal.NamedRecoveryRead.confirmationInputRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using h
  rcases hprot with hPfg | hPfilt
  · exact Block.preceq_trans (Block.preceq_trans hPfg hrootA) hAout
  -- the ghost walk from the anchor passes `P`
  have hsupport : ConeSupport S.E st.T
      (confVotes S.E st slot) (confVotes S.E st slot)
      (confLate S.E st slot) slot rho.honest
      (fun X => Block.Preceq P X) := by
    have hN := confNumerator S.E st slot
    refine coneSupport_of_named_votes (hcom slot) hN.subset_late
      (subset_refl _) (fun y _ _ => hN.no_equivocation y) ?_
    intro x hxCommittee hxHon
    obtain ⟨X, hXerase, hXrun, hXemit⟩ :=
      WeakGoldfish.voterHead_runBlock_and_emits
        S hexec.core hxHon hslotPos hxCommittee hvoteHor
    have hheadMemX : voterHeadAt S rho x slot ∈
        (Internal.NamedRecoveryRead.voteDutyRead S rho x slot).st.core.T := by
      let duty := Internal.NamedRecoveryRead.voteDutyRead S rho x slot
      have hinvPre : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
          (rho.stateBeforeTime S (Protocol.vote_time S.E slot) x).st :=
        (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
          (Protocol.vote_time S.E slot) x).1
      have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg duty.st := by
        simpa only [duty, Internal.NamedRecoveryRead.voteDutyRead,
          NamedActionReads.confirmationReadAt] using
          Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ _ hinvPre
      have hroot : Protocol.get_fg_root duty.st.core.toHealing.toFG ∈
          duty.st.core.T := Proofs.NamedStoreRoots.fg_root_mem duty.st hinv.1.2
      have hanchor : voterAnchorAt S rho x slot ∈ duty.st.core.T :=
        Proofs.NamedConfirmationMembership.runtime_anchor_mem duty.cache
          S.E S.hc duty.st.core.toHealing
          (S.hc.round_of duty.st.core.s) hroot
      have htree : voterCandidateTreeAt S rho x slot ⊆ duty.st.core.T := by
        intro D hD
        exact (Finset.mem_filter.mp
          (Proofs.Records.get_filtered_block_tree_from_subset
            duty.st.core.toHealing.toFG
            (Protocol.voter_processed_block_tree S.E
              duty.st.core.toHealing.toFG.toSG.toGoldfishStore duty.st.core.s) hD)).1
      exact Proofs.Records.ghost_mem_of _ _ hanchor htree
    have hXbody : X ∈ (NamedRun.stateBeforeTime S rho
        (Protocol.vote_time S.E slot) x).st.bodies := by
      have hcoreX : X.erase ∈ (NamedRun.stateBeforeTime S rho
          (Protocol.vote_time S.E slot) x).st.core.T := by
        simpa only [Internal.NamedRecoveryRead.voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock, hXerase] using hheadMemX
      have htree := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
        (Protocol.vote_time S.E slot) x).1.1.1.1
      rw [htree] at hcoreX
      obtain ⟨Y', hY', hY'erase⟩ := Finset.mem_image.mp hcoreX
      obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
        S rho hexec.core.sorted (Protocol.vote_time S.E slot)
      have hY'prefix : Y' ∈ (NamedRun.stateBefore S rho n x).st.bodies := by
        rw [← hn]
        exact hY'
      have hY'run : RunBlock S rho Y' :=
        Proofs.Bridges.runBlock_of_stateBefore_mem S hxHon hY'prefix
      have hY'X : Y' = X := hexec.core.toNamedRootCollisionFree.root_injective
        Y' X hY'run hXrun Y' X (Or.inl (Proofs.NamedAncestry.named_self Y'))
          (Or.inr (Proofs.NamedAncestry.named_self X)) (by
            rw [← Proofs.NamedWire.erase_root Y', ← Proofs.NamedWire.erase_root X,
              hY'erase, hXerase])
      simpa only [hY'X] using hY'
    have hF : Block.Preceq
        (NamedRun.stateBeforeTime S rho
          (Protocol.confirmation_time S.E slot) u).st.core.F X.erase := by
      have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        S rho (Protocol.confirmation_time S.E slot) u
      have hFroot := Proofs.Records.preceq_get_fg_root_of_F
        (st := (NamedRun.stateBeforeTime S rho
          (Protocol.confirmation_time S.E slot) u).st.core.toHealing.toFG) hFJ
      exact Block.preceq_trans (by simpa only [Protocol.Store.toHealing] using hFroot)
        (Block.preceq_trans hrootA (by
          rw [hXerase]
          exact hheads u hu x hxHon))
    obtain ⟨-, hstamp, hfind⟩ := NamedHealthyHeadReady.healthy_head_body_at_read
      S rho hexec.core b0 hexec.healthy x hxHon u hu X
      (Protocol.vote_time S.E slot) (Protocol.support_cutoff S.E slot)
      (Protocol.confirmation_time S.E slot) hXbody
      (by rw [Proofs.Optimistic.vote_time_add_delta])
      (support_cutoff_le_confirmation_time S.E slot)
      ((support_cutoff_le_confirmation_time S.E slot).trans hconfCap) hF
    have hcount : (⟨x, slot, X.erase.root⟩ : GoldfishVote V) ∈
        confVotes S.E st slot := by
      apply canonicalSuffixHonestVoteCounted_of_delivery
        S hexec.core hexec.healthy hslotPos hconfCap u hu _ rfl hxHon hXemit
      exact ⟨X.erase, by simpa only [st, confStore, tickStore] using hfind,
        by simpa only [st, confStore, tickStore] using hstamp⟩
    have hXmem : X.erase ∈
        (NamedRun.stateBeforeTime S rho
          (Protocol.confirmation_time S.E slot) u).st.core.T := by
      exact Proofs.HealingLemmas.find?_mem hfind
    have hXslot : X.erase.slot ≤ slot :=
      Proofs.Optimistic.emitted_vote_head_slot_le_of_store_mem S hexec.core hxHon hu hXemit rfl
        hXmem (by rfl)
    exact ⟨X.erase, by rw [hXerase]; exact hPheads x hxHon,
      hXslot, hcount, by simpa only [st, confStore, tickStore] using hfind⟩
  have hvalid : Protocol.VoteSetValid S.E slot (confLate S.E st slot) := by
    simpa only [st, confStore, tickStore] using
      voteSetValid_confLate_stateBeforeTime S
        hexec.core.toNamedScheduleWellFormed u
          (Protocol.confirmation_time S.E slot) slot
  have hpre : Block.Preceq (confAnchorWith contract S.E S.hc st) P := hAP
  have hpath : ∀ C : Block V, Block.Preceq (confAnchorWith contract S.E S.hc st) C →
      C ≠ confAnchorWith contract S.E S.hc st → Block.Preceq C P →
      C ∈ confTree st := by
    let t := Protocol.confirmation_time S.E slot
    let pre := rho.stateBeforeTime S t u
    have hpc : ParentClosed pre.st.core :=
      Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho t u
    have hFJ : Block.Preceq pre.st.core.F pre.st.core.J :=
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho t u
    have hB : P ∈ confTree st := hPfilt
    intro C hAC _ hCB
    have hBT : P ∈ st.T :=
      Proofs.Records.get_filtered_block_tree_subset st.toHealing.toFG hB
    have hCT : C ∈ st.T := by
      apply Proofs.Records.mem_of_preceq ((parentClosed_iff pre.st.core).mp hpc).2 C P
      · exact hBT
      · exact hCB
    apply Proofs.Records.mem_filtered_of_preceq (st := st.toHealing.toFG) hFJ hB hCT hCB
    refine Block.preceq_trans ?_ hAC
    exact Proofs.HealingSurface.fg_root_preceq_get_sg_root_with_frame
      read.cache S.E S.hc st.toHealing (S.hc.round_of st.s)
  exact Proofs.Optimistic.update_confirmation_preceq_with contract S.E S.hc st slot rho.honest
    hsupport hvalid hpre hpath

#print axioms openingConfirmation_above_of_preceq_openingHeads

set_option maxHeartbeats 400000 in
/-- Seed-free carrier floor: a block below every honest opening head, with no
honest conflict above it, is below every honest SG vote of the round. -/
theorem honestCarriersAbove_of_preceq_openingHeads
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s : Round)
    (hexec : OutageExecution S rho b0 b1)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hmargin : FormationMargin S s b0) (hs : 0 < s)
    (P : Block V) (hno : NoHonestConflictAbove S rho b0 P)
    (hPheads : ∀ w ∈ rho.honest,
      Block.Preceq P (voterHeadAt S rho w (S.hc.opening_slot s))) :
    HonestCarriersAbove S rho P s := by
  have hheads := openingHeads_above_confirmationAnchors
    S rho b0 b1 s hexec hcom hsleep hforming hmargin hs
  have hgenuine := openingConfirmation_genuine_above_anchor
    S rho b0 b1 s hexec hcom hsleep hforming hmargin hs
  have hconf := openingConfirmation_above_of_preceq_openingHeads
    S rho b0 b1 s hexec hcom hsleep hforming hmargin hs P hno hPheads
  have hclear := actionRead_clear_of_preceq_openingHeads
    S rho b0 b1 s hexec hcom hsleep hforming hmargin hs P hPheads
  have hAclear := actionAnchor_clear
    S rho b0 b1 s hexec hcom hsleep hforming hmargin hs
  intro u hu
  have huHon : u ∈ rho.honest :=
    ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u s).mp hu).1
  have hPlive : Block.Preceq P
      (Proofs.HealingSurface.actionReadAt S rho u s).st.core.live_confirmed := by
    change Block.Preceq P (actionStoreAt S rho u s).st.core.live_confirmed
    rw [Proofs.HealingSurface.actionStoreAt_eq_update_confirmation_confStore]
    exact hconf u huHon
  have hAlive : Block.Preceq
      (nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho u s) s)
      (Proofs.HealingSurface.actionReadAt S rho u s).st.core.live_confirmed := by
    rw [actionAnchor_eq_openingConfirmationAnchor]
    change Block.Preceq (confirmationAnchorAt S rho u (S.hc.opening_slot s))
      (actionStoreAt S rho u s).st.core.live_confirmed
    rw [Proofs.HealingSurface.actionStoreAt_eq_update_confirmation_confStore]
    exact (hgenuine u huHon).2
  have hcompat := Block.compatible_of_preceq_common
    (hheads u huHon u huHon) (hPheads u huHon)
  rcases (show Block.Preceq (confirmationAnchorAt S rho u (S.hc.opening_slot s)) P ∨
      Block.Preceq P (confirmationAnchorAt S rho u (S.hc.opening_slot s)) by
        simpa only [Block.compatible, Bool.or_eq_true] using hcompat) with hAP | hPA
  · have hAP' : Block.Preceq
        (nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho u s) s) P := by
      rw [actionAnchor_eq_openingConfirmationAnchor]
      exact hAP
    exact preceq_actionSGBlockAt_of_anchor_live_clear S rho u s P hAP' hPlive
      (hclear u huHon)
  · have hPA' : Block.Preceq P
        (nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho u s) s) := by
      rw [actionAnchor_eq_openingConfirmationAnchor]
      exact hPA
    exact Block.preceq_trans hPA'
      (actionAnchor_preceq_actionSGBlockAt_of_live_clear
        S rho u s hAlive (hAclear u huHon))

#print axioms honestCarriersAbove_of_preceq_openingHeads

/-- A block below every honest opening head has a named copy held by every
honest node at the round action (its own head is held, bodies are
parent-closed, and the strict read is monotone). -/
theorem held_of_preceq_openingHeads
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s : Round)
    (hexec : OutageExecution S rho b0 b1)
    (P : Block V)
    (hPheads : ∀ w ∈ rho.honest,
      Block.Preceq P (voterHeadAt S rho w (S.hc.opening_slot s))) :
    ∀ u ∈ rho.honest, ∃ Pn : NamedBlock V, Pn.erase = P ∧
      Pn ∈ (NamedRun.stateBeforeTime S rho (S.a s) u).st.bodies ∧
      NamedRun.blockInRun S rho Pn := by
  intro u hu
  let slot := S.hc.opening_slot s
  have hheadMem : voterHeadAt S rho u slot ∈
      (Internal.NamedRecoveryRead.voteDutyRead S rho u slot).st.core.T := by
    let duty := Internal.NamedRecoveryRead.voteDutyRead S rho u slot
    have hinvPre : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
        (rho.stateBeforeTime S (Protocol.vote_time S.E slot) u).st :=
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
        (Protocol.vote_time S.E slot) u).1
    have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg duty.st := by
      simpa only [duty, Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt] using
        Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ _ hinvPre
    have hroot : Protocol.get_fg_root duty.st.core.toHealing.toFG ∈
        duty.st.core.T := Proofs.NamedStoreRoots.fg_root_mem duty.st hinv.1.2
    have hanchor : voterAnchorAt S rho u slot ∈ duty.st.core.T :=
      Proofs.NamedConfirmationMembership.runtime_anchor_mem duty.cache
        S.E S.hc duty.st.core.toHealing
        (S.hc.round_of duty.st.core.s) hroot
    have htree : voterCandidateTreeAt S rho u slot ⊆ duty.st.core.T := by
      intro D hD
      exact (Finset.mem_filter.mp
        (Proofs.Records.get_filtered_block_tree_from_subset
          duty.st.core.toHealing.toFG
          (Protocol.voter_processed_block_tree S.E
            duty.st.core.toHealing.toFG.toSG.toGoldfishStore duty.st.core.s) hD)).1
    exact Proofs.Records.ghost_mem_of _ _ hanchor htree
  have hcore : voterHeadAt S rho u slot ∈ (NamedRun.stateBeforeTime S rho
      (Protocol.vote_time S.E slot) u).st.core.T := by
    simpa only [Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hheadMem
  have hcohVote : Proofs.NamedStore.Coherent S.E S.cfg
      (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E slot) u).st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (Protocol.vote_time S.E slot) u).1.1.1
  rw [hcohVote.1] at hcore
  obtain ⟨Y, hY, hYerase⟩ := Finset.mem_image.mp hcore
  obtain ⟨Pn, hPnY, hPnErase⟩ :=
    NamedOutageHistory.ReadyHeadReturn.named_ancestor_of_erase P Y
      (by rw [hYerase]; exact hPheads u hu)
  have hPnVote : Pn ∈ (NamedRun.stateBeforeTime S rho
      (Protocol.vote_time S.E slot) u).st.bodies :=
    ancestor_body_mem' hcohVote.2.2.1 hY hPnY
  have hPnHeld : Pn ∈ (NamedRun.stateBeforeTime S rho
      (Protocol.confirmation_time S.E slot) u).st.bodies :=
    (q10_strict_body_carry S rho hexec.core.toNamedScheduleWellFormed u
      (vote_time_le_confirmation_time S.E slot) hPnVote).1
  rw [opening_confirmation_time_eq_action] at hPnHeld
  refine ⟨Pn, hPnErase, hPnHeld, ?_⟩
  obtain ⟨i, hi, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho hexec.core.sorted (S.a s)
  rw [hi] at hPnHeld
  exact Proofs.Bridges.runBlock_of_stateBefore_mem S hu hPnHeld

#print axioms held_of_preceq_openingHeads

set_option maxHeartbeats 400000 in
/-- The exact round-`s` arm of `HonestConfirmedAtOrAbove` follows from the
stable-round carrier floor. -/
theorem stableAt_honestConfirmedAtOrAbove_exactRound
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s : Round) (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : NamedOutageEntry.SlashableBound S rho)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hstable : stableAt S rho v s P) (hs : 0 < s)
    (a : NamedAttestation V) (t : Time)
    (ha : a.val_index ∈ rho.honest)
    (hem : NamedRun.emits S rho a.val_index (.attest a) t)
    (haround : a.round = s)
    (key : BlockId) (hkey : a.confirmed = some key)
    (K : NamedBlock V) (hKrun : NamedRun.blockInRun S rho K)
    (hKroot : K.root = key) :
    Block.Preceq P K.erase := by
  have hfloor := stableAt_honestCarriersAbove_sameRound
    S rho b0 b1 v s P hexec hslash hcom hsleep hforming
      hv hmargin hstable hs
  exact honestConfirmedAtOrAbove_exactRound_of_carrierFloor
    S rho s P hexec.core hfloor a t ha hem haround key hkey K hKrun hKroot

#print axioms stableAt_honestConfirmedAtOrAbove_exactRound





end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
