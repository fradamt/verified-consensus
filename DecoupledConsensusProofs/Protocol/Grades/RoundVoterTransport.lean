module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.PostOutage
public import DecoupledConsensusProofs.Protocol.Store.BoundaryRows
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Assembly
public import DecoupledConsensusProofs.Execution.SGArrivalDeadline
public import DecoupledConsensusProofs.Protocol.Grades.HealthyHeadReady
public import Mathlib.Algebra.Order.Archimedean.Basic

@[expose] public section

/-!
# Round-voter transport after GST

This module transports an honest round-`r` action attestation into the early
and late interpreted views for round `r + 1`. The interfaces below are the 
restatement surface for. No public statement is changed.
-/


namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Internal Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem successor_window_lo : ∀ s e : Nat, 1 ≤ e → s + 1 - e ≤ s := by
  intro s e he
  omega

private theorem early_g1_le_domain_g1 (S : Setup V) (r : Round) :
    early S.E S.hc r .g1 ≤ domain S.E S.hc r .g1 :=
  (q10_early_g1_le_domain_g2 S r).trans
    (q10_domain_g2_lt_domain_g1 S r).le

private theorem phase_domain_nonneg (S : Setup V) {r : Round}
    (hr : 0 < r) {p : Phase} (hp : p = .g1 ∨ p = .g2) :
    (0 : Time) ≤ domain S.E S.hc r p := by
  rcases hp with rfl | rfl
  · rw [base_domain_g1_eq_opening]
    exact base_opening_nonneg S r
  · have hnat : (2 : Nat) ≤ r * S.hc.R := by
      have hmul : (1 : Nat) * S.hc.R ≤ r * S.hc.R :=
        Nat.mul_le_mul_right S.hc.R hr
      rw [one_mul] at hmul
      exact S.hc.R_ge_two.trans hmul
    have hcast : (2 : Time) ≤ ((r * S.hc.R : Nat) : Time) := by
      exact_mod_cast hnat
    unfold domain opening Protocol.proposal_time Env.t
      Protocol.HealConfig.opening_slot slotStart
    simp only [Phase.domainOffset]
    push_cast
    nlinarith [S.E.Δ_pos]

/-- The successor stable interval contains its G1 domain read. -/
theorem domain_g1_le_next_domain_g2 (S : Setup V) (r : Round) :
    domain S.E S.hc r .g1 ≤ domain S.E S.hc (r + 1) .g2 := by
  have hR : (2 : Time) ≤ ((S.hc.R : Nat) : Time) := by
    exact_mod_cast S.hc.R_ge_two
  unfold domain opening Protocol.proposal_time Env.t
    Protocol.HealConfig.opening_slot slotStart
  simp only [Phase.domainOffset]
  push_cast
  nlinarith [S.E.Δ_pos]

/-- Membership in `honestRoundVoters` has an exact named emission witness. -/
theorem honestRoundVoter_emits
    (S : Setup V) (rho : NamedRun V) {u : V} {r : Round}
    (hu : u ∈ honestRoundVoters S rho r) :
    ∃ a : NamedAttestation V, a.round = r ∧ a.val_index = u ∧
      NamedRun.emits S rho u (.attest a) (S.a r) := by
  obtain ⟨_, a, hval, hround, hemit⟩ :=
    (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u r).mp hu
  exact ⟨a, hround, hval, hemit⟩

/-- An honest round emission confirms the carrier computed at its action
read. -/
theorem honest_emitted_round_confirmed
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (u : V) (hu : u ∈ rho.honest) (r : Round) (hhor : S.a r ≤ rho.horizon)
    {a : NamedAttestation V} (haround : a.round = r)
    (hemit : NamedRun.emits S rho u (.attest a) (S.a r)) :
    a.confirmed = some (Proofs.HealingSurface.actionSGBlockAt S rho u r).root := by
  have hawake : (S.node u).awake r = true := by
    simpa only [haround] using Proofs.Optimistic.emits_attest_awake S hemit
  have hcanonical := Proofs.HealingSurface.honest_emits_exact_actionAttestationAt_of_awake
    S core.toNamedScheduleWellFormed hu r hawake hhor
  have ha : a = Proofs.HealingSurface.actionAttestationAt S rho u r := by
    apply Proofs.Optimistic.emits_attest_unique S core.toNamedScheduleWellFormed
      hemit hcanonical
    simpa only [haround] using
      (Proofs.HealingSurface.actionAttestationAt_shape S rho u r).2.1.symm
  rw [ha]
  exact (Proofs.HealingSurface.actionAttestationAt_shape S rho u r).2.2

/-- A post-outage certificate floors all honest carriers in its round. The
K6 case split supplies the active-tree arm when finality has not passed `P`. -/
theorem carriersAbove_of_postOutageAbove
    (S : Setup V) (rho : NamedRun V) (P : Block V) (r : Round)
    (core : NamedAdmissibleCore S rho) (hr : 0 < r)
    (hhor : S.a r ≤ rho.horizon) (h : PostOutageAbove S rho P r)
    (hK6 : ∀ u ∈ rho.honest,
      Block.Preceq P
          (Protocol.get_fg_root
            (NamedActionReads.actionReadAt S rho u r).st.core.toHealing.toFG) ∨
        P ∈ Protocol.get_filtered_block_tree
          (NamedActionReads.actionReadAt S rho u r).st.core.toHealing.toFG) :
    HonestCarriersAbove S rho P r := by
  intro u hu
  have huHon : u ∈ rho.honest :=
    ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u r).mp hu).1
  obtain ⟨a, haround, _, hemit⟩ := honestRoundVoter_emits S rho hu
  rcases hK6 u huHon with hroot | htree
  · exact Block.preceq_trans hroot (by
      simpa only [Proofs.HealingSurface.actionStoreAt] using
        Proofs.HealingSurface.actionFGRoot_preceq_actionSGBlockAt S rho u r)
  · exact (h.emitted_vote_floor_of_finalized_or_active S rho P r core
      u huHon hr hhor haround hemit (Or.inr htree)).2

/-- The final outage invariant floors the honest carriers without converting
its checkpoint frame back to raw strict-domain freezes. -/
theorem carriersAbove_of_sg_clause
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (Pn : NamedBlock V) (r : Round) (hexec : OutageExecution S rho b0 b1)
    (hr : 0 < r)
    (hsg : ∀ v ∈ rho.honest,
      let n := NamedRun.readAt S rho (domain S.E S.hc r .g1) v
      Block.Preceq Pn.erase n.st.core.F ∨
        ∃ raw : Block V,
          (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g2 =
            some (some raw) ∧
          Block.Preceq Pn.erase raw)
    (hjoint : S.a r ≤ rho.horizon → ∀ v ∈ rho.honest,
      (Block.Preceq Pn.erase
          (Protocol.get_fg_root
            (checkpoint S rho v r).st.core.toHealing.toFG) ∨
        Pn.erase ∈ Protocol.get_filtered_block_tree
          (checkpoint S rho v r).st.core.toHealing.toFG) ∧
      Block.compatible Pn.erase (checkpoint S rho v r).st.core.F = true) :
    HonestCarriersAbove S rho Pn.erase r := by
  intro u hu
  have huHon : u ∈ rho.honest :=
    ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u r).mp hu).1
  obtain ⟨a, _, _, hemit⟩ := honestRoundVoter_emits S rho hu
  obtain ⟨i, hi, _⟩ := hemit
  have hmem : NamedEvent.tick u (S.a r) ∈ rho.events :=
    List.mem_iff_getElem?.mpr ⟨i, hi⟩
  have hhor : S.a r ≤ rho.horizon :=
    (hexec.core.toNamedScheduleWellFormed.in_horizon _ hmem).2
  have hsgAction := sg_field_at_checkpoint_of_clauses S rho b0 Pn r
    hexec.core hsg (hjoint hhor) u huHon
  rcases hsgAction with hroot | ⟨raw, G, hframe, hactive, hPG⟩
  · exact Block.preceq_trans hroot (by
      simpa only [Internal.NamedJointOutage.checkpoint,
        Internal.NamedStableChainOutage.roundConfirmationRead,
        Internal.NamedOutageEntry.confirmationReadAt,
        Proofs.HealingSurface.actionStoreAt, Proofs.HealingSurface.actionReadAt,
        NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
        Protocol.NamedDuties.update_confirmation_with] using
          Proofs.HealingSurface.actionFGRoot_preceq_actionSGBlockAt S rho u r)
  · let action := NamedActionReads.actionReadAt S rho u r
    have hframeAction : (DecoupledConsensusModel.Protocol.readFrame action.cache
        action.st.core.toHealing r).g2 = some (some raw) := by
      simpa only [action, Internal.NamedJointOutage.checkpoint,
        Internal.NamedStableChainOutage.roundConfirmationRead,
        Internal.NamedOutageEntry.confirmationReadAt,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
        NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
        Protocol.NamedDuties.update_confirmation_with] using hframe
    have hro : S.hc.round_of
        (Internal.NamedJointOutage.checkpoint S rho u r).st.core.toHealing.s = r := by
      simpa only [Protocol.Store.toHealing] using
        (Proofs.HealingLemmas.round_of_slotOf_a S r)
    unfold Internal.NamedStableChainOutage.activeG2
      DecoupledConsensusModel.Protocol.frameSGCandidate at hactive
    rw [hro, hframe] at hactive
    simp only [Option.bind_some, id_eq] at hactive
    have hactiveTree : DecoupledConsensusModel.Protocol.activePrefix
        (Protocol.get_filtered_block_tree action.st.core.toHealing.toFG) raw =
        some G := by
      simpa only [action, Internal.NamedJointOutage.checkpoint,
        Internal.NamedStableChainOutage.roundConfirmationRead,
        Internal.NamedOutageEntry.confirmationReadAt,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
        NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
        Protocol.NamedDuties.update_confirmation_with,
        Protocol.update_confirmation_with] using hactive
    have hactiveAction : ((DecoupledConsensusModel.Protocol.readFrame action.cache
        action.st.core.toHealing r).g2.bind id).bind
          (DecoupledConsensusModel.Protocol.activePrefix
            (Protocol.get_filtered_block_tree action.st.core.toHealing.toFG)) =
        some G := by
      rw [hframeAction]
      simpa only [Option.bind_some, id_eq] using hactiveTree
    have hclosed : DecoupledConsensusModel.Protocol.allClosed
        (DecoupledConsensusModel.Protocol.readFrame action.cache action.st.core.toHealing r) = true := by
      simpa only [action] using
          Proofs.HealingSurface.actionFrame_allClosed S hexec.core huHon hr hhor
    have hQ : Internal.PhaseGrades.nodeQ2 S action r = some G := by
      simp only [Internal.PhaseGrades.nodeQ2, Internal.PhaseGrades.nodeRead,
        NamedProfile.gradeContract, DecoupledConsensusModel.Protocol.frameContract,
        Protocol.grade2_block_with, DecoupledConsensusModel.Protocol.frameGradeRead,
        DecoupledConsensusModel.Protocol.grade2Block, hclosed, if_true]
      exact hactiveAction
    exact Proofs.HealingSurface.preceq_actionSGBlockAt_of_actionQ2 S hexec.core
      huHon hr hhor hQ hPG

/-- The invariant form of `carriersAbove_of_sg_clause`. -/
theorem carriersAbove_of_roundInvariant
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (Pn : NamedBlock V) (r : Round) (hexec : OutageExecution S rho b0 b1)
    (hinv : Internal.NamedJointOutage.RoundInvariant S rho b0 Pn r) :
    HonestCarriersAbove S rho Pn.erase r := by
  exact carriersAbove_of_sg_clause S rho b0 b1 Pn r hexec
    hinv.included.1 hinv.sg (fun hhor => hinv.fg hhor)

/-- The final outage invariant makes every stable root written in its remaining
round comparable with the protected prefix. -/
theorem confirmationDutyRoot_comparable_of_sg_clause
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (Pn : NamedBlock V) (r : Round) (hexec : OutageExecution S rho b0 b1)
    (hr : 0 < r)
    (hsg : ∀ v ∈ rho.honest,
      let n := NamedRun.readAt S rho (domain S.E S.hc r .g1) v
      Block.Preceq Pn.erase n.st.core.F ∨
        ∃ raw : Block V,
          (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g2 =
            some (some raw) ∧ Block.Preceq Pn.erase raw)
    (w : V) (hw : w ∈ rho.honest) (u : Time)
    (hlo : domain S.E S.hc r .g2 ≤ u)
    (hhi : u < domain S.E S.hc (r + 1) .g2)
    (hcut : u = Protocol.support_cutoff S.E (S.E.slotOf u))
    (hK6next : Block.Preceq Pn.erase
        (Protocol.get_fg_root
          (Proofs.HealingSurface.relativeG2Read S rho (r + 1) w).st.core.toHealing.toFG) ∨
      Pn.erase ∈ Internal.PhaseGrades.filteredTree
        (Proofs.HealingSurface.relativeG2Read S rho (r + 1) w))
    (hfg : Block.compatible Pn.erase (Protocol.get_fg_root
      (NamedActionReads.confirmationReadAt S rho w u).st.core.toHealing.toFG) = true)
    {G : Block V}
    (hG : dutyStableRoot S
      (NamedActionReads.confirmationReadAt S rho w u) = some G) :
    Block.Preceq Pn.erase G ∨ Block.Preceq G Pn.erase := by
  let start := domain S.E S.hc r .g1 + 1
  let stop := domain S.E S.hc (r + 1) .g2
  let n := NamedActionReads.confirmationReadAt S rho w u
  have hu0 : (0 : Time) ≤ u :=
    (phase_domain_nonneg S hr (Or.inr rfl)).trans hlo
  have hround := support_cutoff_round_of_domain_window S r u hlo hhi hcut
  have hopen : opening S.E S.hc r < u := by
    have h := opening_lt_support_cutoff S u hu0 hcut
    simpa only [clockRoundAt, hround] using h
  have hstartu : start ≤ u := by
    dsimp only [start]
    rw [domain_g1_eq_opening]
    exact Int.add_one_le_iff.mpr hopen
  have hustop : u ≤ opening S.E S.hc (r + 1) :=
    by
      rw [← domain_g1_eq_opening]
      exact (hhi.trans (q10_domain_g2_lt_domain_g1 S (r + 1))).le
  have hFuStop : Block.Preceq
      (NamedRun.stateBeforeTime S rho u w).st.core.F
      (NamedRun.stateBeforeTime S rho stop w).st.core.F :=
    incl_strict_F_mono S rho hexec.core.toNamedScheduleWellFormed w hhi.le
  have hcompat : Block.compatible Pn.erase
      (NamedRun.stateBeforeTime S rho u w).st.core.F = true := by
    rcases hK6next with hroot | hPtreeStop
    · have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        S rho stop w
      have hFroot := Proofs.Records.preceq_get_fg_root_of_F
        (st := (NamedRun.stateBeforeTime S rho stop w).st.core.toHealing.toFG)
        (by simpa only [Protocol.Store.toHealing] using hFJ)
      have hroot' : Block.Preceq Pn.erase
          (Protocol.get_fg_root
            (NamedRun.stateBeforeTime S rho stop w).st.core.toHealing.toFG) := by
        simpa only [stop, Proofs.HealingSurface.relativeG2Read,
          Internal.PhaseGrades.filteredTree] using hroot
      exact Block.compatible_of_preceq_common hroot'
        (Block.preceq_trans hFuStop hFroot)
    · have hFstop := q10_filtered_F (by
          simpa only [stop, Proofs.HealingSurface.relativeG2Read,
            Internal.PhaseGrades.filteredTree] using hPtreeStop)
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr (Block.preceq_trans hFuStop hFstop)
  rcases hsg w hw with hPF | ⟨raw, hframe, hPraw⟩
  · have hPFstart : Block.Preceq Pn.erase
        (NamedRun.stateBeforeTime S rho start w).st.core.F := by
      dsimp only [start]
      rw [← readAt_eq_succ S rho (domain S.E S.hc r .g1)]
      exact hPF
    have hPFu : Block.Preceq Pn.erase
        (NamedRun.stateBeforeTime S rho u w).st.core.F :=
      Block.preceq_trans hPFstart
        (incl_strict_F_mono S rho hexec.core.toNamedScheduleWellFormed w hstartu)
    have hPFn : Block.Preceq Pn.erase n.st.core.F := by
      simpa only [n, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, Protocol.NamedStore.setClock] using hPFu
    have hFJ : Block.Preceq n.st.core.F n.st.core.J := by
      simpa only [n, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, Protocol.NamedStore.setClock] using
          Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho u w
    exact Or.inl (Block.preceq_trans hPFn
      (Block.preceq_trans
        (Proofs.Records.preceq_get_fg_root_of_F
          (st := n.st.core.toHealing.toFG)
          (by simpa only [Protocol.Store.toHealing] using hFJ))
        (fgRoot_preceq_dutyStableRoot S n hG)))
  · have hframeStart : (DecoupledConsensusModel.Protocol.readFrame
        (NamedRun.stateBeforeTime S rho start w).cache
        (NamedRun.stateBeforeTime S rho start w).st.core.toHealing r).g2 =
        some (some raw) := by
      dsimp only [start]
      rw [← readAt_eq_succ S rho (domain S.E S.hc r .g1)]
      exact hframe
    have hframeU : (DecoupledConsensusModel.Protocol.readFrame
        (NamedRun.stateBeforeTime S rho u w).cache
        (NamedRun.stateBeforeTime S rho u w).st.core.toHealing r).g2 =
        some (some (DecoupledConsensusModel.Protocol.clipGrade raw
          (NamedRun.stateBeforeTime S rho u w).st.core.F)) := by
      have hpersist := FrameForward.frame_phase_persists_in_round S rho
        hexec.core w r .g2 start u hstartu hustop (some raw) hframeStart
      simpa only [DecoupledConsensusModel.Protocol.phaseResult, DecoupledConsensusModel.Protocol.clipResult,
        Option.map_some] using hpersist
    have hprepared := frame_phase_prepared_eq S rho w r .g2 u hround _ hframeU
    have hframeN : (DecoupledConsensusModel.Protocol.readFrame n.cache
        n.st.core.toHealing r).g2 =
        some (some (DecoupledConsensusModel.Protocol.clipGrade raw
          (NamedRun.stateBeforeTime S rho u w).st.core.F)) := by
      simpa only [n, DecoupledConsensusModel.Protocol.phaseResult] using hprepared
    have hPclip : Block.Preceq Pn.erase
        (DecoupledConsensusModel.Protocol.clipGrade raw
          (NamedRun.stateBeforeTime S rho u w).st.core.F) :=
      (q10_retained_prefix raw _ Pn.erase hcompat).mpr hPraw
    have hnround : S.hc.round_of n.st.core.s = r := by
      simpa only [n, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, Protocol.NamedStore.setClock] using hround
    apply duty_root_comparable_of_frame S n
    · rw [hnround]
      exact hframeN
    · exact hPclip
    · exact hfg
    · exact hG



/-- An honest raw input is the projection of the sender's unique attestation
for that round. The raw window also gives both round bounds. -/
theorem honest_rawInput_is_own_round_vote
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (cut cutoff : Time) (w : V) (_hw : w ∈ rho.honest)
    {u : V} (hu : u ∈ rho.honest) {r : Round} {y : Protocol.SGVote V}
    (hy : y ∈ rawInputs
      (NamedRun.stateBeforeTime S rho cut w).st.core.toHealing.gradeView
      S.hc.η_SG (r + 1) cutoff u) :
    ∃ a : NamedAttestation V,
      a.round = y.round ∧ a.val_index = u ∧
      NamedRun.emits S rho u (.attest a) (S.a y.round) ∧
      y.val_index = a.val_index ∧ y.confirmed = a.confirmed ∧
      emittedInRound S rho u y.round = true ∧
      r + 1 - S.hc.η_SG ≤ y.round ∧ y.round ≤ r := by
  obtain ⟨a, hval, hround, hproj, hwindow, _, hemit⟩ :=
    rawInputs_trace S rho core.toNamedScheduleWellFormed
      core.toNamedUnforgeable cut cutoff w S.hc.η_SG (r + 1) u hu hy
  obtain ⟨hlower, hupper⟩ := window_bounds hwindow
  refine ⟨a, hround, hval, ?_, ?_, ?_, ?_, hlower, ?_⟩
  · simpa only [hround] using hemit
  · rw [← hproj, sgVote_val]
  · rw [← hproj, sgVote_confirmed]
  · apply (Proofs.NamedOutageInputs.emittedInRound_iff S rho u y.round).mpr
    exact ⟨a, hval, hround, by simpa only [hround] using hemit⟩
  · exact Nat.le_of_lt_succ (by simpa only [Nat.add_comm] using hupper)

omit [Fintype V] in
/-- If `P` reaches the stable output and has not passed finality, finality is
below `P`. Both blocks are ancestors of the stable output. -/
theorem finalized_preceq_of_stable_caseB
    (st : Protocol.Store V) {P : Block V}
    (hstable : Block.Preceq P (Protocol.get_stable st))
    (hB : ¬ Block.Preceq P st.F) : Block.Preceq st.F P := by
  have hFstable : Block.Preceq st.F (Protocol.get_stable st) := by
    unfold Protocol.get_stable
    split
    · assumption
    · exact Block.preceq_self _
  rcases Block.preceq_linear hFstable hstable with hFP | hPF
  · exact hFP
  · exact False.elim (hB hPF)

/-- The G2 transport at its real network deadline. This is the constructive
half of T3 and keeps the exact action carrier in the conclusion. -/
theorem honestRoundVote_interpreted_at_g2_reader_of_deadline
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1) (P : Block V) (r : Round)
    (hdeadline : max (S.a r) S.E.t_GST + S.E.Δ ≤
      early S.E S.hc (r + 1) .g2)
    (hcarriers : HonestCarriersAbove S rho P r)
    (hstableG2 : ∀ w ∈ rho.honest, Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core))
    (w : V) (hw : w ∈ rho.honest)
    (hhor : domain S.E S.hc (r + 1) .g2 ≤ rho.horizon)
    (hB : ¬ Block.Preceq P
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core.F)
    {u : V} (hu : u ∈ honestRoundVoters S rho r) :
    ∃ y ∈ interpretedInputs
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g2) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g2) w).st.core.F
        S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) .g2) u,
      y.round = r ∧
      y.confirmed = some (Proofs.HealingSurface.actionSGBlockAt S rho u r).root ∧
      Block.find?
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g2) w).st.core.T
        (Proofs.HealingSurface.actionSGBlockAt S rho u r).root =
          some (Proofs.HealingSurface.actionSGBlockAt S rho u r) ∧
      Block.Preceq P (Proofs.HealingSurface.actionSGBlockAt S rho u r) := by
  have huHon : u ∈ rho.honest :=
    ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u r).mp hu).1
  obtain ⟨a, haround, hval, hemit⟩ := honestRoundVoter_emits S rho hu
  have hactionHor : S.a r ≤ rho.horizon :=
    (action_le_domain S S.hc.R_ge_three (Nat.lt_succ_self r)).trans hhor
  have hPH := hcarriers u hu
  have haconfirmed := honest_emitted_round_confirmed S rho hexec.core
    u huHon r hactionHor haround hemit
  obtain ⟨i, hi, _, hbody⟩ := Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
  dsimp at hbody
  obtain ⟨K, hKstaged, haK⟩ := hbody
  have hKindex : K ∈ (NamedRun.stateBefore S rho i u).st.bodies := by
    change K ∈ (NamedRun.stateBefore S rho i u).st.bodies at hKstaged
    exact hKstaged
  have hstate := NamedActionSources.action_read_index S rho
    hexec.core.toNamedScheduleWellFormed i u r hi
  have hKsource : K ∈
      (NamedRun.stateBeforeTime S rho (S.a r) u).st.bodies := by
    rw [← hstate]
    exact hKindex
  have hKrun : NamedRun.blockInRun S rho K :=
    held_blockInRun S rho hexec.core.toNamedScheduleWellFormed
      u huHon (S.a r) hKsource
  let H := Proofs.HealingSurface.actionSGBlockAt S rho u r
  have hHmem : H ∈ (Proofs.HealingSurface.actionStoreAt S rho u r).st.core.T := by
    exact Proofs.HealingSurface.actionSGBlockAt_mem_actionStore S rho u r
  have htree := (Proofs.HealingSurface.actionRead_invariant S rho u r).1.1.1
  rw [htree] at hHmem
  obtain ⟨D, hD, hDerase⟩ := Finset.mem_image.mp hHmem
  have hDsource : D ∈
      (NamedRun.stateBeforeTime S rho (S.a r) u).st.bodies := by
    change D ∈ (NamedRun.stateBeforeTime S rho (S.a r) u).st.bodies
    exact hD
  have hDrun : NamedRun.blockInRun S rho D :=
    held_blockInRun S rho hexec.core.toNamedScheduleWellFormed
      u huHon (S.a r) hDsource
  have hDKroot : D.root = K.root := by
    rw [← Proofs.NamedWire.erase_root D, hDerase, ← Option.some.inj (haconfirmed.symm.trans haK)]
  have hDK : D = K :=
    hexec.core.toNamedRootCollisionFree.root_injective D K hDrun hKrun D K
      (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self K)) hDKroot
  have hKerased : K.erase = H := by
    rw [← hDK, hDerase]
  let target := NamedRun.stateBeforeTime S rho
    (domain S.E S.hc (r + 1) .g2) w
  have hPstable : Block.Preceq P (Protocol.get_stable target.st.core) := by
    exact hstableG2 w hw
  have hFP : Block.Preceq target.st.core.F P := by
    exact finalized_preceq_of_stable_caseB target.st.core hPstable
      (by simpa only [target] using hB)
  have hFK : Block.Preceq target.st.core.F K.erase := by
    rw [hKerased]
    exact Block.preceq_trans hFP hPH
  obtain ⟨_, hstamp, hfind⟩ :=
    NamedHealthyHeadReady.healthy_head_body_at_read_after_gst S rho hexec.core
      u huHon w hw K (S.a r) (early S.E S.hc (r + 1) .g2)
      (domain S.E S.hc (r + 1) .g2) hKsource hdeadline
      (early_le_domain S (r + 1))
      ((early_le_domain S (r + 1)).trans hhor) hFK
  have hem : NamedRun.emits S rho a.val_index (.attest a) (S.a a.round) := by
    simpa only [hval, haround] using hemit
  have hvalHon : a.val_index ∈ rho.honest := by
    simpa only [hval] using huHon
  have hdeadline' : max (S.a a.round) S.E.t_GST + S.E.Δ ≤
      early S.E S.hc (a.round + 1) .g2 := by
    simpa only [haround] using hdeadline
  obtain ⟨td, hlo, hhi, j, hcall⟩ :=
    hexec.core.toNamedSynchrony.broadcast a.val_index hvalHon (.attest a)
      (S.a a.round) hem w hw
      (hdeadline'.trans ((early_le_domain S (a.round + 1)).trans
        (by simpa only [haround] using hhor))) rfl
  have htdEarly : td < early S.E S.hc (r + 1) .g2 :=
    hhi.trans_le (by simpa only [haround] using hdeadline')
  have hraw : Protocol.sgVote a.erase ∈ rawInputs
      target.st.core.toHealing.gradeView S.hc.η_SG (r + 1)
        (early S.E S.hc (r + 1) .g2) u := by
    have hraw' := SGArrivalDeadline.outage_emitted_sg_raw_at_next_g2
      S rho b0 b1 hexec hvalHon hem hlo
        (by simpa only [haround] using htdEarly) hcall
    simpa only [target, haround, hval] using hraw'
  have hconf : (Protocol.sgVote a.erase).confirmed = some K.erase.root := by
    rw [sgVote_confirmed, haK, Proofs.NamedWire.erase_root]
  have hcompat : Block.compatible K.erase target.st.core.F = true := by
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr hFK
  have hready : bodyReady target.st.core.toHealing.gradeView target.st.core.F
      (early S.E S.hc (r + 1) .g2) (Protocol.sgVote a.erase) = true := by
    simp only [bodyReady, hconf]
    change (match Block.find? target.st.core.T K.erase.root with
      | none => false
      | some head => stampedBefore target.st.core.timestamp_block
          (early S.E S.hc (r + 1) .g2) head &&
            Block.compatible head target.st.core.F) = true
    rw [hfind, Bool.and_eq_true]
    exact ⟨hstamp, hcompat⟩
  refine ⟨Protocol.sgVote a.erase, Finset.mem_filter.mpr ⟨hraw, hready⟩, ?_⟩
  refine ⟨?_, ?_, ?_, hPH⟩
  · simpa only [sgVote_round, haround]
  · rw [sgVote_confirmed, haconfirmed]
  · simpa only [target, hKerased, Proofs.NamedWire.erase_root] using hfind





/-- The  transport at the G1 domain read, under the stable floor produced
by the successor G2 clause and its confirmation-write carry. -/
theorem honestRoundVote_interpreted_at_g1_reader
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1) (P : Block V) (r : Round)
    (hpost : b1 ≤ S.a r) (hcarriers : HonestCarriersAbove S rho P r)
    (hstableG1 : ∀ w ∈ rho.honest, Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g1) w).st.core))
    (w : V) (hw : w ∈ rho.honest)
    (hhor : domain S.E S.hc (r + 1) .g1 ≤ rho.horizon)
    (hB : ¬ Block.Preceq P
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g1) w).st.core.F)
    {u : V} (hu : u ∈ honestRoundVoters S rho r) :
    ∃ y ∈ interpretedInputs
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g1) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g1) w).st.core.F
        S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) .g1) u,
      y.round = r ∧
      y.confirmed = some (Proofs.HealingSurface.actionSGBlockAt S rho u r).root ∧
      Block.find?
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g1) w).st.core.T
        (Proofs.HealingSurface.actionSGBlockAt S rho u r).root =
          some (Proofs.HealingSurface.actionSGBlockAt S rho u r) ∧
      Block.Preceq P (Proofs.HealingSurface.actionSGBlockAt S rho u r) := by
  have huHon : u ∈ rho.honest :=
    ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u r).mp hu).1
  obtain ⟨a, haround, hval, hemit⟩ := honestRoundVoter_emits S rho hu
  have hactionHor : S.a r ≤ rho.horizon :=
    (action_le_domain S S.hc.R_ge_three (Nat.lt_succ_self r)).trans
      ((q10_domain_g2_lt_domain_g1 S (r + 1)).le.trans hhor)
  have hPH := hcarriers u hu
  have haconfirmed := honest_emitted_round_confirmed S rho hexec.core
    u huHon r hactionHor haround hemit
  obtain ⟨i, hi, _, hbody⟩ := Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
  dsimp at hbody
  obtain ⟨K, hKstaged, haK⟩ := hbody
  have hKindex : K ∈ (NamedRun.stateBefore S rho i u).st.bodies := by
    change K ∈ (NamedRun.stateBefore S rho i u).st.bodies at hKstaged
    exact hKstaged
  have hstate := NamedActionSources.action_read_index S rho
    hexec.core.toNamedScheduleWellFormed i u r hi
  have hKsource : K ∈
      (NamedRun.stateBeforeTime S rho (S.a r) u).st.bodies := by
    rw [← hstate]
    exact hKindex
  have hKrun : NamedRun.blockInRun S rho K :=
    held_blockInRun S rho hexec.core.toNamedScheduleWellFormed
      u huHon (S.a r) hKsource
  let H := Proofs.HealingSurface.actionSGBlockAt S rho u r
  have hHmem : H ∈ (Proofs.HealingSurface.actionStoreAt S rho u r).st.core.T := by
    exact Proofs.HealingSurface.actionSGBlockAt_mem_actionStore S rho u r
  have htree := (Proofs.HealingSurface.actionRead_invariant S rho u r).1.1.1
  rw [htree] at hHmem
  obtain ⟨D, hD, hDerase⟩ := Finset.mem_image.mp hHmem
  have hDsource : D ∈
      (NamedRun.stateBeforeTime S rho (S.a r) u).st.bodies := by
    change D ∈ (NamedRun.stateBeforeTime S rho (S.a r) u).st.bodies
    exact hD
  have hDrun : NamedRun.blockInRun S rho D :=
    held_blockInRun S rho hexec.core.toNamedScheduleWellFormed
      u huHon (S.a r) hDsource
  have hDKroot : D.root = K.root := by
    rw [← Proofs.NamedWire.erase_root D, hDerase, ← Option.some.inj (haconfirmed.symm.trans haK)]
  have hDK : D = K :=
    hexec.core.toNamedRootCollisionFree.root_injective D K hDrun hKrun D K
      (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self K)) hDKroot
  have hKerased : K.erase = H := by
    rw [← hDK, hDerase]
  let target := NamedRun.stateBeforeTime S rho
    (domain S.E S.hc (r + 1) .g1) w
  have hPstable : Block.Preceq P (Protocol.get_stable target.st.core) := by
    simpa only [target] using hstableG1 w hw
  have hFP : Block.Preceq target.st.core.F P := by
    exact finalized_preceq_of_stable_caseB target.st.core hPstable
      (by simpa only [target] using hB)
  have hFK : Block.Preceq target.st.core.F K.erase := by
    rw [hKerased]
    exact Block.preceq_trans hFP hPH
  have hgst : S.E.t_GST ≤ S.a r := hexec.gst.trans hpost
  have hdeadline : max (S.a r) S.E.t_GST + S.E.Δ ≤
      early S.E S.hc (r + 1) .g1 := by
    rw [max_eq_left hgst]
    exact (action_delta_le_early S S.hc.R_ge_three
      (Nat.lt_succ_self r)).trans (q10_early_g2_le_early_g1 S (r + 1))
  obtain ⟨_, hstamp, hfind⟩ :=
    NamedHealthyHeadReady.healthy_head_body_at_read_after_gst S rho hexec.core
      u huHon w hw K (S.a r) (early S.E S.hc (r + 1) .g1)
      (domain S.E S.hc (r + 1) .g1) hKsource hdeadline
      (early_g1_le_domain_g1 S (r + 1))
      ((early_g1_le_domain_g1 S (r + 1)).trans hhor) hFK
  have hem : NamedRun.emits S rho a.val_index (.attest a) (S.a a.round) := by
    simpa only [hval, haround] using hemit
  have hvalHon : a.val_index ∈ rho.honest := by
    simpa only [hval] using huHon
  let healthy := healthyWindowDelivery_after_gst S rho hexec.core
  obtain ⟨td, hlo, hhi, j, hcall⟩ := healthy.broadcast a.val_index hvalHon
    (.attest a) (S.a a.round) hem w hw (by simpa only [haround] using hgst)
      (by simpa only [haround] using
        (action_delta_le_early S S.hc.R_ge_three
          (Nat.lt_succ_self r)).trans
            ((q10_early_g2_le_early_g1 S (r + 1)).trans
            ((early_g1_le_domain_g1 S (r + 1)).trans hhor))) rfl
  have hrow := Proofs.NamedSGArrival.honest_row_after_call S rho
    hexec.core.toNamedScheduleWellFormed hexec.core.toNamedUnforgeable
    hvalHon hem hcall hlo hhi
  obtain ⟨e, he, _, het⟩ := hcall.2
  obtain ⟨_, stamp, hstampBound, hstampEvent⟩ :=
    Proofs.NamedSGArrival.held_row_own_and_stamp_at_event S rho
      hexec.core.toNamedScheduleWellFormed he w a.round a hrow
  have hactionDeadline : S.a a.round + S.E.Δ ≤
      early S.E S.hc (r + 1) .g1 := by
    simpa only [haround] using
      (action_delta_le_early S S.hc.R_ge_three
        (Nat.lt_succ_self r)).trans (q10_early_g2_le_early_g1 S (r + 1))
  have htdEarly : td < early S.E S.hc (r + 1) .g1 :=
    hhi.trans_le hactionDeadline
  have heEarly : e.time < early S.E S.hc (r + 1) .g1 := by
    simpa only [het] using htdEarly
  have heCut : e.time < domain S.E S.hc (r + 1) .g1 :=
    heEarly.trans_le (early_g1_le_domain_g1 S (r + 1))
  let n := (rho.events.filter (fun e => decide
    (e.time < domain S.E S.hc (r + 1) .g1))).length
  have hread : NamedRun.stateBeforeTime S rho
      (domain S.E S.hc (r + 1) .g1) = NamedRun.stateBefore S rho n := by
    exact Proofs.Optimistic.stateBeforeTime_eq_take S
      hexec.core.toNamedScheduleWellFormed _
  have hjn : j < n := by
    by_contra hnot
    have hnj : n ≤ j := Nat.le_of_not_gt hnot
    have hle := Proofs.Optimistic.le_time_of_index_ge S
      hexec.core.toNamedScheduleWellFormed
      (t := domain S.E S.hc (r + 1) .g1) (j := j) (e := e) hnj he
    exact (not_le_of_gt heCut) hle
  have hrowN := Proofs.NamedSGArrival.stateBefore_sg_row_stamp_mono S rho w
    (Nat.succ_le_of_lt hjn) hrow
  have hrowCut : a ∈ target.st.sg_rows a.round := by
    dsimp only [target]
    rw [hread]
    exact hrowN.1
  have hstampCut : target.st.core.timestamp_sg_vote
      (Protocol.sgVote a.erase) = some (stamp : Stamp) := by
    dsimp only [target]
    rw [hread]
    exact hrowN.2.trans hstampEvent
  have hoccur : occurrenceBefore
      (target.st.core.timestamp_sg_vote (Protocol.sgVote a.erase))
      (early S.E S.hc (r + 1) .g1) = true := by
    simp only [hstampCut, occurrenceBefore, decide_eq_true_eq]
    exact WithBot.coe_lt_coe.mpr (hstampBound.trans_lt heEarly)
  have hcoh :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
      (domain S.E S.hc (r + 1) .g1) w).1.1.1
  have hpool := NamedAdmission.pool_view_mem target.st hcoh.2.2.2.1 a hrowCut
  have hsg : Protocol.sgVote a.erase ∈
      target.st.core.toHealing.gradeView.sg_votes a.round :=
    Finset.mem_image_of_mem Protocol.sgVote hpool
  have hwindow : r ∈ Protocol.latest_window S.hc.η_SG (r + 1) := by
    apply mem_latest_window
    · exact successor_window_lo r S.hc.η_SG S.hc.η_SG_ge_one
    · exact Nat.lt_succ_self r
  have hraw : Protocol.sgVote a.erase ∈ rawInputs
      target.st.core.toHealing.gradeView S.hc.η_SG (r + 1)
        (early S.E S.hc (r + 1) .g1) u := by
    simp only [rawInputs, Finset.mem_filter]
    refine ⟨Finset.mem_biUnion.mpr ⟨a.round, List.mem_toFinset.mpr ?_, hsg⟩, ?_, hoccur⟩
    · simpa only [haround] using hwindow
    · rw [sgVote_val, hval]
  have hconf : (Protocol.sgVote a.erase).confirmed = some K.erase.root := by
    rw [sgVote_confirmed, haK, Proofs.NamedWire.erase_root]
  have hcompat : Block.compatible K.erase target.st.core.F = true := by
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr hFK
  have hready : bodyReady target.st.core.toHealing.gradeView target.st.core.F
      (early S.E S.hc (r + 1) .g1) (Protocol.sgVote a.erase) = true := by
    simp only [bodyReady, hconf]
    change (match Block.find? target.st.core.T K.erase.root with
      | none => false
      | some head => stampedBefore target.st.core.timestamp_block
          (early S.E S.hc (r + 1) .g1) head &&
            Block.compatible head target.st.core.F) = true
    rw [hfind, Bool.and_eq_true]
    exact ⟨hstamp, hcompat⟩
  refine ⟨Protocol.sgVote a.erase, Finset.mem_filter.mpr ⟨hraw, hready⟩, ?_⟩
  refine ⟨?_, ?_, ?_, hPH⟩
  · simpa only [sgVote_round, haround]
  · rw [sgVote_confirmed, haconfirmed]
  · simpa only [target, hKerased, Proofs.NamedWire.erase_root] using hfind


/-- Honest raw tokens have one confirmed key in each round. -/
theorem honest_rawView_clean
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (cut cutoff : Time) (w : V) (hw : w ∈ rho.honest)
    {u : V} (hu : u ∈ rho.honest) (r k : Round) :
    CleanFrom
      (DecoupledConsensusModel.Protocol.rawView
        (NamedRun.stateBeforeTime S rho cut w).st.core.toHealing.gradeView
        S.hc.η_SG (r + 1) cutoff u) k := by
  intro x hx y hy _ hround
  simp only [DecoupledConsensusModel.Protocol.rawView] at hx hy
  obtain ⟨xv, hxv, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨yv, hyv, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨a, haroundA, _, hemitA, _, hconfirmedA, _, _, _⟩ :=
    honest_rawInput_is_own_round_vote S rho core cut cutoff w hw hu hxv
  obtain ⟨b, haroundB, _, hemitB, _, hconfirmedB, _, _, _⟩ :=
    honest_rawInput_is_own_round_vote S rho core cut cutoff w hw hu hyv
  have hab : a = b :=
    NamedOutageProvenance.emitted_same_round_unique S rho
      core.toNamedScheduleWellFormed hemitA hemitB (by
        rw [haroundA, haroundB]
        simpa only [DecoupledConsensusModel.Protocol.token] using hround)
  show xv.confirmed = yv.confirmed
  rw [hconfirmedA, hconfirmedB, hab]

/-- Honest round-`r` voters are positive at G2 under the real relay deadline. -/
theorem honestRoundVoters_positive_at_g2_read_of_deadline
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1) (P : Block V) (r : Round)
    (hdeadline : max (S.a r) S.E.t_GST + S.E.Δ ≤
      early S.E S.hc (r + 1) .g2)
    (hcarriers : HonestCarriersAbove S rho P r)
    (hstableG2 : ∀ w ∈ rho.honest, Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core))
    (w : V) (hw : w ∈ rho.honest)
    (hhor : domain S.E S.hc (r + 1) .g2 ≤ rho.horizon)
    (hB : ¬ Block.Preceq P
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core.F) :
    honestRoundVoters S rho r ⊆ Finset.univ.filter fun u =>
      DecoupledConsensusModel.Protocol.positive
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g2) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g2) w).st.core.F
        S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) .g2)
        (late S.E S.hc (r + 1) .g2) u P = true := by
  intro u hu
  have huHon : u ∈ rho.honest :=
    ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u r).mp hu).1
  obtain ⟨y, hy, hyround, hyconfirmed, hyfind, hPH⟩ :=
    honestRoundVote_interpreted_at_g2_reader_of_deadline
      S rho b0 b1 hexec P r hdeadline hcarriers hstableG2 w hw hhor hB hu
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ u, ?_⟩
  simp only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq]
  refine ⟨DecoupledConsensusModel.Protocol.token y, Finset.mem_image_of_mem _ hy, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have hzraw := (Finset.mem_filter.mp hz).1
    obtain ⟨_, _, _, _, _, _, _, _, hzupper⟩ :=
      honest_rawInput_is_own_round_vote S rho hexec.core
        (domain S.E S.hc (r + 1) .g2) (early S.E S.hc (r + 1) .g2)
        w hw huHon hzraw
    simpa only [DecoupledConsensusModel.Protocol.token, hyround] using hzupper
  · change Protocol.head_covers
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core.T P y.confirmed = true
    rw [hyconfirmed]
    simp only [Protocol.head_covers, hyfind]
    exact hPH
  · exact honest_rawView_clean S rho hexec.core
      (domain S.E S.hc (r + 1) .g2) (late S.E S.hc (r + 1) .g2)
      w hw huHon r (DecoupledConsensusModel.Protocol.token y).round
  · intro x hx hlt
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have hzraw := (Finset.mem_filter.mp hz).1
    obtain ⟨_, _, _, _, _, _, _, _, hzupper⟩ :=
      honest_rawInput_is_own_round_vote S rho hexec.core
        (domain S.E S.hc (r + 1) .g2) (late S.E S.hc (r + 1) .g2)
        w hw huHon hzraw
    exfalso
    exact (Nat.not_lt_of_ge hzupper) (by
      simpa only [DecoupledConsensusModel.Protocol.token, hyround] using hlt)

/-- The honest round-`r` voters are positive at the round-`r+1` G2 read. -/
theorem honestRoundVoters_positive_at_g2_read_of_floor
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1) (P : Block V) (r : Round)
    (hpost : b1 ≤ S.a r) (hcarriers : HonestCarriersAbove S rho P r)
    (hstableG2 : ∀ w ∈ rho.honest, Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core))
    (w : V) (hw : w ∈ rho.honest)
    (hhor : domain S.E S.hc (r + 1) .g2 ≤ rho.horizon)
    (hB : ¬ Block.Preceq P
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core.F) :
    honestRoundVoters S rho r ⊆ Finset.univ.filter fun u =>
      DecoupledConsensusModel.Protocol.positive
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g2) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g2) w).st.core.F
        S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) .g2)
        (late S.E S.hc (r + 1) .g2) u P = true := by
  have hgst : S.E.t_GST ≤ S.a r := hexec.gst.trans hpost
  have hdeadline : max (S.a r) S.E.t_GST + S.E.Δ ≤
      early S.E S.hc (r + 1) .g2 := by
    rw [max_eq_left hgst]
    exact action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r)
  exact honestRoundVoters_positive_at_g2_read_of_deadline
    S rho b0 b1 hexec P r hdeadline hcarriers hstableG2 w hw hhor hB

/-- Interval-facing wrapper for pointwise G2 positivity. -/
theorem honestRoundVoters_positive_at_g2_read
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1) (P : Block V) (r : Round)
    (hpost : b1 ≤ S.a r) (hcarriers : HonestCarriersAbove S rho P r)
    (hstable : ∀ w ∈ rho.honest, ∀ t,
      domain S.E S.hc r .g2 ≤ t → t ≤ domain S.E S.hc (r + 1) .g2 →
      Block.Preceq P
        (Protocol.get_stable (NamedRun.stateBeforeTime S rho t w).st.core))
    (w : V) (hw : w ∈ rho.honest)
    (hhor : domain S.E S.hc (r + 1) .g2 ≤ rho.horizon)
    (hB : ¬ Block.Preceq P
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core.F) :
    honestRoundVoters S rho r ⊆ Finset.univ.filter fun u =>
      DecoupledConsensusModel.Protocol.positive
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g2) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g2) w).st.core.F
        S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) .g2)
        (late S.E S.hc (r + 1) .g2) u P = true := by
  exact honestRoundVoters_positive_at_g2_read_of_floor S rho b0 b1
    hexec P r hpost hcarriers
      (fun w hw => hstable w hw _
        (base_domain_g2_mono S (Nat.le_succ r)) le_rfl)
      w hw hhor hB

/-- Every honest G2 opponent is stale under the real relay deadline. -/
theorem opposing_at_g2_read_subset_of_deadline
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1) (P : Block V) (r : Round)
    (hdeadline : max (S.a r) S.E.t_GST + S.E.Δ ≤
      early S.E S.hc (r + 1) .g2)
    (hcarriers : HonestCarriersAbove S rho P r)
    (hstableG2 : ∀ w ∈ rho.honest, Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core))
    (w : V) (hw : w ∈ rho.honest)
    (hhor : domain S.E S.hc (r + 1) .g2 ≤ rho.horizon)
    (hB : ¬ Block.Preceq P
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core.F) :
    (Finset.univ.filter fun u => DecoupledConsensusModel.Protocol.opposing
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core.F
      S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) .g2)
      (late S.E S.hc (r + 1) .g2) u P = true) ⊆
        (Finset.univ \ rho.honest) ∪ staleHistoricalVoters S rho (r + 1) := by
  intro u hu
  by_cases huHon : u ∈ rho.honest
  · refine Finset.mem_union_right _ ?_
    have hopp := (Finset.mem_filter.mp hu).2
    simp only [DecoupledConsensusModel.Protocol.opposing, decide_eq_true_eq] at hopp
    rcases hopp with ⟨x, hx, hdom, hnotcover⟩ |
      ⟨x, hx, y, hy, _, hround, hkey⟩
    · simp only [DecoupledConsensusModel.Protocol.readyView, Finset.mem_image] at hx
      obtain ⟨z, hz, hzx⟩ := hx
      rw [← hzx] at hdom hnotcover
      have hzraw := (Finset.mem_filter.mp hz).1
      obtain ⟨a, haround, hval, hemit, _, hconfirmed, _, hlower, hupper⟩ :=
        honest_rawInput_is_own_round_vote S rho hexec.core
          (domain S.E S.hc (r + 1) .g2) (late S.E S.hc (r + 1) .g2)
          w hw huHon hzraw
      have hwindow : z.round ∈ Protocol.latest_window S.hc.η_SG (r + 1) :=
        mem_latest_window hlower (Nat.lt_succ_of_le hupper)
      by_cases hvote : u ∈ honestRoundVoters S rho r
      · obtain ⟨earlyVote, hearly, hearlyRound, _, hfind, _⟩ :=
          honestRoundVote_interpreted_at_g2_reader_of_deadline
            S rho b0 b1 hexec P r hdeadline hcarriers hstableG2
              w hw hhor hB hvote
        have hrz : r ≤ z.round := by
          simpa only [DecoupledConsensusModel.Protocol.token, hearlyRound] using
            hdom (DecoupledConsensusModel.Protocol.token earlyVote)
              (Finset.mem_image_of_mem DecoupledConsensusModel.Protocol.token hearly)
        have hzround : z.round = r := Nat.le_antisymm hupper hrz
        have har : a.round = r := haround.trans hzround
        have hemr : NamedRun.emits S rho u (.attest a) (S.a r) := by
          simpa only [hzround] using hemit
        have hPA := hcarriers u hvote
        have haconfirmed := honest_emitted_round_confirmed S rho hexec.core
          u huHon r
          ((action_le_domain S S.hc.R_ge_three
            (Nat.lt_succ_self r)).trans hhor)
          har hemr
        exact False.elim (hnotcover (by
          change Protocol.head_covers
            (NamedRun.stateBeforeTime S rho
              (domain S.E S.hc (r + 1) .g2) w).st.core.T
            P z.confirmed = true
          rw [hconfirmed, haconfirmed]
          simp only [Protocol.head_covers, hfind]
          exact hPA))
      · have hzvote : u ∈ honestRoundVoters S rho z.round :=
          (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u z.round).mpr
            ⟨huHon, a, hval, haround, hemit⟩
        have hnotPrevious : u ∉ honestRoundVoters S rho (r + 1 - 1) := by
          simpa only [Nat.add_sub_cancel] using hvote
        exact Proofs.NamedOutageInputs.stale_of_eligible_vote S rho
          hwindow hzvote hnotPrevious
    · have hclean := honest_rawView_clean S rho hexec.core
        (domain S.E S.hc (r + 1) .g2) (late S.E S.hc (r + 1) .g2)
        w hw huHon r 0
      exact False.elim (hkey (hclean x hx y hy (Nat.zero_le _) hround))
  · exact Finset.mem_union_left _
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, huHon⟩)

/-- Every honest G2 opponent is a stale historical voter. -/
theorem opposing_at_g2_read_subset_of_floor
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1) (P : Block V) (r : Round)
    (hpost : b1 ≤ S.a r) (hcarriers : HonestCarriersAbove S rho P r)
    (hstableG2 : ∀ w ∈ rho.honest, Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core))
    (w : V) (hw : w ∈ rho.honest)
    (hhor : domain S.E S.hc (r + 1) .g2 ≤ rho.horizon)
    (hB : ¬ Block.Preceq P
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core.F) :
    (Finset.univ.filter fun u => DecoupledConsensusModel.Protocol.opposing
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core.F
      S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) .g2)
      (late S.E S.hc (r + 1) .g2) u P = true) ⊆
        (Finset.univ \ rho.honest) ∪ staleHistoricalVoters S rho (r + 1) := by
  have hgst : S.E.t_GST ≤ S.a r := hexec.gst.trans hpost
  have hdeadline : max (S.a r) S.E.t_GST + S.E.Δ ≤
      early S.E S.hc (r + 1) .g2 := by
    rw [max_eq_left hgst]
    exact action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r)
  exact opposing_at_g2_read_subset_of_deadline
    S rho b0 b1 hexec P r hdeadline hcarriers hstableG2 w hw hhor hB

/-- Interval-facing wrapper for pointwise G2 opposition containment. -/
theorem opposing_at_g2_read_subset
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1) (P : Block V) (r : Round)
    (hpost : b1 ≤ S.a r) (hcarriers : HonestCarriersAbove S rho P r)
    (hstable : ∀ w ∈ rho.honest, ∀ t,
      domain S.E S.hc r .g2 ≤ t → t ≤ domain S.E S.hc (r + 1) .g2 →
      Block.Preceq P
        (Protocol.get_stable (NamedRun.stateBeforeTime S rho t w).st.core))
    (w : V) (hw : w ∈ rho.honest)
    (hhor : domain S.E S.hc (r + 1) .g2 ≤ rho.horizon)
    (hB : ¬ Block.Preceq P
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core.F) :
    (Finset.univ.filter fun u => DecoupledConsensusModel.Protocol.opposing
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core.F
      S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) .g2)
      (late S.E S.hc (r + 1) .g2) u P = true) ⊆
        (Finset.univ \ rho.honest) ∪ staleHistoricalVoters S rho (r + 1) := by
  exact opposing_at_g2_read_subset_of_floor S rho b0 b1 hexec P r
    hpost hcarriers
      (fun w hw => hstable w hw _
        (base_domain_g2_mono S (Nat.le_succ r)) le_rfl)
      w hw hhor hB



/-- The honest round-`r` voters are positive at the round-`r+1` G1 read. -/
theorem honestRoundVoters_positive_at_g1_read
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1) (P : Block V) (r : Round)
    (hpost : b1 ≤ S.a r) (hcarriers : HonestCarriersAbove S rho P r)
    (hstableG1 : ∀ w ∈ rho.honest, Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g1) w).st.core))
    (w : V) (hw : w ∈ rho.honest)
    (hhor : domain S.E S.hc (r + 1) .g1 ≤ rho.horizon)
    (hB : ¬ Block.Preceq P
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g1) w).st.core.F) :
    honestRoundVoters S rho r ⊆ Finset.univ.filter fun u =>
      DecoupledConsensusModel.Protocol.positive
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g1) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g1) w).st.core.F
        S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) .g1)
        (late S.E S.hc (r + 1) .g1) u P = true := by
  intro u hu
  have huHon : u ∈ rho.honest :=
    ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u r).mp hu).1
  obtain ⟨y, hy, hyround, hyconfirmed, hyfind, hPH⟩ :=
    honestRoundVote_interpreted_at_g1_reader S rho b0 b1 hexec P r
      hpost hcarriers hstableG1 w hw hhor hB hu
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ u, ?_⟩
  simp only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq]
  refine ⟨DecoupledConsensusModel.Protocol.token y, Finset.mem_image_of_mem _ hy, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have hzraw := (Finset.mem_filter.mp hz).1
    obtain ⟨_, _, _, _, _, _, _, _, hzupper⟩ :=
      honest_rawInput_is_own_round_vote S rho hexec.core
        (domain S.E S.hc (r + 1) .g1) (early S.E S.hc (r + 1) .g1)
        w hw huHon hzraw
    simpa only [DecoupledConsensusModel.Protocol.token, hyround] using hzupper
  · change Protocol.head_covers
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g1) w).st.core.T P y.confirmed = true
    rw [hyconfirmed]
    simp only [Protocol.head_covers, hyfind]
    exact hPH
  · exact honest_rawView_clean S rho hexec.core
      (domain S.E S.hc (r + 1) .g1) (late S.E S.hc (r + 1) .g1)
      w hw huHon r (DecoupledConsensusModel.Protocol.token y).round
  · intro x hx hlt
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have hzraw := (Finset.mem_filter.mp hz).1
    obtain ⟨_, _, _, _, _, _, _, _, hzupper⟩ :=
      honest_rawInput_is_own_round_vote S rho hexec.core
        (domain S.E S.hc (r + 1) .g1) (late S.E S.hc (r + 1) .g1)
        w hw huHon hzraw
    exfalso
    exact (Nat.not_lt_of_ge hzupper) (by
      simpa only [DecoupledConsensusModel.Protocol.token, hyround] using hlt)

/-- Every honest G1 opponent is a stale historical voter. -/
theorem opposing_at_g1_read_subset
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1) (P : Block V) (r : Round)
    (hpost : b1 ≤ S.a r) (hcarriers : HonestCarriersAbove S rho P r)
    (hstableG1 : ∀ w ∈ rho.honest, Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g1) w).st.core))
    (w : V) (hw : w ∈ rho.honest)
    (hhor : domain S.E S.hc (r + 1) .g1 ≤ rho.horizon)
    (hB : ¬ Block.Preceq P
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g1) w).st.core.F) :
    (Finset.univ.filter fun u => DecoupledConsensusModel.Protocol.opposing
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g1) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g1) w).st.core.F
      S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) .g1)
      (late S.E S.hc (r + 1) .g1) u P = true) ⊆
        (Finset.univ \ rho.honest) ∪ staleHistoricalVoters S rho (r + 1) := by
  intro u hu
  by_cases huHon : u ∈ rho.honest
  · refine Finset.mem_union_right _ ?_
    have hopp := (Finset.mem_filter.mp hu).2
    simp only [DecoupledConsensusModel.Protocol.opposing, decide_eq_true_eq] at hopp
    rcases hopp with ⟨x, hx, hdom, hnotcover⟩ |
      ⟨x, hx, y, hy, _, hround, hkey⟩
    · simp only [DecoupledConsensusModel.Protocol.readyView, Finset.mem_image] at hx
      obtain ⟨z, hz, hzx⟩ := hx
      rw [← hzx] at hdom hnotcover
      have hzraw := (Finset.mem_filter.mp hz).1
      obtain ⟨a, haround, hval, hemit, _, hconfirmed, _, hlower, hupper⟩ :=
        honest_rawInput_is_own_round_vote S rho hexec.core
          (domain S.E S.hc (r + 1) .g1) (late S.E S.hc (r + 1) .g1)
          w hw huHon hzraw
      have hwindow : z.round ∈ Protocol.latest_window S.hc.η_SG (r + 1) :=
        mem_latest_window hlower (Nat.lt_succ_of_le hupper)
      by_cases hvote : u ∈ honestRoundVoters S rho r
      · obtain ⟨earlyVote, hearly, hearlyRound, _, hfind, _⟩ :=
          honestRoundVote_interpreted_at_g1_reader S rho b0 b1 hexec P r
            hpost hcarriers hstableG1 w hw hhor hB hvote
        have hrz : r ≤ z.round := by
          simpa only [DecoupledConsensusModel.Protocol.token, hearlyRound] using
            hdom (DecoupledConsensusModel.Protocol.token earlyVote)
              (Finset.mem_image_of_mem DecoupledConsensusModel.Protocol.token hearly)
        have hzround : z.round = r := Nat.le_antisymm hupper hrz
        have har : a.round = r := haround.trans hzround
        have hemr : NamedRun.emits S rho u (.attest a) (S.a r) := by
          simpa only [hzround] using hemit
        have hPA := hcarriers u hvote
        have haconfirmed := honest_emitted_round_confirmed S rho hexec.core
          u huHon r
          ((action_le_domain S S.hc.R_ge_three
            (Nat.lt_succ_self r)).trans
              ((q10_domain_g2_lt_domain_g1 S (r + 1)).le.trans hhor))
          har hemr
        exact False.elim (hnotcover (by
          change Protocol.head_covers
            (NamedRun.stateBeforeTime S rho
              (domain S.E S.hc (r + 1) .g1) w).st.core.T
            P z.confirmed = true
          rw [hconfirmed, haconfirmed]
          simp only [Protocol.head_covers, hfind]
          exact hPA))
      · have hzvote : u ∈ honestRoundVoters S rho z.round :=
          (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u z.round).mpr
            ⟨huHon, a, hval, haround, hemit⟩
        have hnotPrevious : u ∉ honestRoundVoters S rho (r + 1 - 1) := by
          simpa only [Nat.add_sub_cancel] using hvote
        exact Proofs.NamedOutageInputs.stale_of_eligible_vote S rho
          hwindow hzvote hnotPrevious
    · have hclean := honest_rawView_clean S rho hexec.core
        (domain S.E S.hc (r + 1) .g1) (late S.E S.hc (r + 1) .g1)
        w hw huHon r 0
      exact False.elim (hkey (hclean x hx y hy (Nat.zero_le _) hround))
  · exact Finset.mem_union_left _
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, huHon⟩)



/- At either successor domain read, carrier votes form a raw phase root above
`P`. The G2 arm uses the preceding stable interval. The G1 arm consumes the
stable floor produced after the G2 root. -/
theorem clauses_at_reader_of_carriersAbove_of_outageExecution
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1) (P : Block V) (r : Round)
    (hpost : b1 ≤ S.a r)
    (hcarriers : HonestCarriersAbove S rho P r)
    (hstable : ∀ w ∈ rho.honest, ∀ t,
      domain S.E S.hc r .g2 ≤ t → t ≤ domain S.E S.hc (r + 1) .g2 →
      Block.Preceq P
        (Protocol.get_stable (NamedRun.stateBeforeTime S rho t w).st.core))
    (hmajority : GradeFormingMajority S rho (r + 1))
    (p : Phase) (hp : p = .g1 ∨ p = .g2)
    (hstableG1 : p = .g1 → ∀ w ∈ rho.honest, Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g1) w).st.core))
    (w : V) (hw : w ∈ rho.honest)
    (hhor : domain S.E S.hc (r + 1) p ≤ rho.horizon) :
    Block.Preceq P
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) p) w).st.core.F ∨
      ∃ R, DecoupledConsensusModel.Protocol.freezeRoot S.E
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) p) w).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) p) w).st.core.F
          S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) p)
          (late S.E S.hc (r + 1) p) = some R ∧ Block.Preceq P R := by
  by_cases hB : Block.Preceq P
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) p) w).st.core.F
  · exact Or.inl hB
  · have hpositive : honestRoundVoters S rho r ⊆ Finset.univ.filter fun u =>
        DecoupledConsensusModel.Protocol.positive
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) p) w).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) p) w).st.core.F
          S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) p)
          (late S.E S.hc (r + 1) p) u P = true := by
      rcases hp with rfl | rfl
      · exact honestRoundVoters_positive_at_g1_read S rho b0 b1 hexec P r
          hpost hcarriers (hstableG1 rfl) w hw hhor hB
      · exact honestRoundVoters_positive_at_g2_read S rho b0 b1 hexec P r
          hpost hcarriers hstable w hw hhor hB
    have hopposing : (Finset.univ.filter fun u =>
        DecoupledConsensusModel.Protocol.opposing
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) p) w).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) p) w).st.core.F
          S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) p)
          (late S.E S.hc (r + 1) p) u P = true) ⊆
          (Finset.univ \ rho.honest) ∪ staleHistoricalVoters S rho (r + 1) := by
      rcases hp with rfl | rfl
      · exact opposing_at_g1_read_subset S rho b0 b1 hexec P r hpost
          hcarriers (hstableG1 rfl) w hw hhor hB
      · exact opposing_at_g2_read_subset S rho b0 b1 hexec P r hpost
          hcarriers hstable w hw hhor hB
    have hgrade := Proofs.HealingSurface.phaseGrade_of_gradeFormingMajority S rho
      (r + 1)
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) p) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) p) w).st.core.F P
      (early S.E S.hc (r + 1) p) (late S.E S.hc (r + 1) p)
      hmajority (by simpa only [Nat.add_sub_cancel] using hpositive) hopposing
    have hvoters : (honestRoundVoters S rho r).Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro heq
      have hlt := hmajority
      unfold GradeFormingMajority at hlt
      rw [Nat.add_sub_cancel, heq] at hlt
      exact Nat.not_lt_zero _ (by
        simpa only [Electorate.weightOf, Finset.sum_empty] using hlt)
    obtain ⟨u, hu⟩ := hvoters
    have hupos := (Finset.mem_filter.mp (hpositive hu)).2
    simp only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq,
      DecoupledConsensusModel.Protocol.Supports] at hupos
    obtain ⟨tok, htok, _, hcover, _, _⟩ := hupos
    simp only [DecoupledConsensusModel.Protocol.readyView, Finset.mem_image] at htok
    obtain ⟨y, hy, rfl⟩ := htok
    change Protocol.head_covers
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) p) w).st.core.T P y.confirmed = true at hcover
    simp only [Protocol.head_covers] at hcover
    cases hconfirmed : y.confirmed with
    | none => simp [hconfirmed] at hcover
    | some root =>
      cases hfind : Block.find?
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) p) w).st.core.T root with
      | none => simp [hconfirmed, hfind] at hcover
      | some H =>
        have hHmem := Proofs.HealingLemmas.find?_mem hfind
        have hPH : Block.Preceq P H := by
          simpa [hconfirmed, hfind] using hcover
        have hclosed := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
          (domain S.E S.hc (r + 1) p) w
        have hPmem : P ∈ (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) p) w).st.core.T :=
          Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hclosed).2 P H hHmem hPH
        obtain ⟨R, hR, hPR⟩ := q10_freeze_of_graded S.E
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) p) w).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) p) w).st.core.F S.hc.η_SG (r + 1)
          (q10_early_le_late S (r + 1) p) hPmem hgrade
        exact Or.inr ⟨R, hR, hPR⟩




/- At either successor domain read, any execution regime that supplies the
carrier-grade inputs forms a raw phase root above `P`. -/
theorem clause_at_reader_of_carriersAbove
    (S : Setup V) (rho : NamedRun V) (_core : NamedAdmissibleCore S rho)
    (P : Block V) (r : Round)
    (hmajority : GradeFormingMajority S rho (r + 1))
    (p : Phase) (hp : p = .g1 ∨ p = .g2)
    (hformation : ∀ w ∈ rho.honest,
      domain S.E S.hc (r + 1) p ≤ rho.horizon →
      ¬ Block.Preceq P
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) p) w).st.core.F →
      honestRoundVoters S rho r ⊆ Finset.univ.filter (fun u =>
        DecoupledConsensusModel.Protocol.positive
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) p) w).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) p) w).st.core.F
          S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) p)
          (late S.E S.hc (r + 1) p) u P = true) ∧
      (Finset.univ.filter fun u => DecoupledConsensusModel.Protocol.opposing
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) p) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) p) w).st.core.F
        S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) p)
        (late S.E S.hc (r + 1) p) u P = true) ⊆
          (Finset.univ \ rho.honest) ∪ staleHistoricalVoters S rho (r + 1))
    (w : V) (hw : w ∈ rho.honest)
    (hhor : domain S.E S.hc (r + 1) p ≤ rho.horizon) :
    Block.Preceq P
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) p) w).st.core.F ∨
      ∃ R, DecoupledConsensusModel.Protocol.freezeRoot S.E
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) p) w).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) p) w).st.core.F
          S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) p)
          (late S.E S.hc (r + 1) p) = some R ∧ Block.Preceq P R := by
  by_cases hB : Block.Preceq P
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) p) w).st.core.F
  · exact Or.inl hB
  · obtain ⟨hpositive, hopposing⟩ :=
      hformation w hw hhor hB
    have hgrade := Proofs.HealingSurface.phaseGrade_of_gradeFormingMajority S rho
      (r + 1)
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) p) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) p) w).st.core.F P
      (early S.E S.hc (r + 1) p) (late S.E S.hc (r + 1) p)
      hmajority (by simpa only [Nat.add_sub_cancel] using hpositive) hopposing
    have hvoters : (honestRoundVoters S rho r).Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro heq
      have hlt := hmajority
      unfold GradeFormingMajority at hlt
      rw [Nat.add_sub_cancel, heq] at hlt
      exact Nat.not_lt_zero _ (by
        simpa only [Electorate.weightOf, Finset.sum_empty] using hlt)
    obtain ⟨u, hu⟩ := hvoters
    have hupos := (Finset.mem_filter.mp (hpositive hu)).2
    simp only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq,
      DecoupledConsensusModel.Protocol.Supports] at hupos
    obtain ⟨tok, htok, _, hcover, _, _⟩ := hupos
    simp only [DecoupledConsensusModel.Protocol.readyView, Finset.mem_image] at htok
    obtain ⟨y, hy, rfl⟩ := htok
    change Protocol.head_covers
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) p) w).st.core.T P y.confirmed = true at hcover
    simp only [Protocol.head_covers] at hcover
    cases hconfirmed : y.confirmed with
    | none => simp [hconfirmed] at hcover
    | some root =>
      cases hfind : Block.find?
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) p) w).st.core.T root with
      | none => simp [hconfirmed, hfind] at hcover
      | some H =>
        have hHmem := Proofs.HealingLemmas.find?_mem hfind
        have hPH : Block.Preceq P H := by
          simpa [hconfirmed, hfind] using hcover
        have hclosed := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
          (domain S.E S.hc (r + 1) p) w
        have hPmem : P ∈ (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) p) w).st.core.T :=
          Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hclosed).2 P H hHmem hPH
        obtain ⟨R, hR, hPR⟩ := q10_freeze_of_graded S.E
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) p) w).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) p) w).st.core.F S.hc.η_SG (r + 1)
          (q10_early_le_late S (r + 1) p) hPmem hgrade
        exact Or.inr ⟨R, hR, hPR⟩

/-- The G2 instance when recovery, not the send time, controls delivery. -/
theorem clause_at_g2_of_deadline
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1) (P : Block V) (r : Round)
    (hdeadline : max (S.a r) S.E.t_GST + S.E.Δ ≤
      early S.E S.hc (r + 1) .g2)
    (hcarriers : HonestCarriersAbove S rho P r)
    (hstableG2 : ∀ w ∈ rho.honest, Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core))
    (hmajority : GradeFormingMajority S rho (r + 1))
    (w : V) (hw : w ∈ rho.honest)
    (hhor : domain S.E S.hc (r + 1) .g2 ≤ rho.horizon) :
    Block.Preceq P
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g2) w).st.core.F ∨
      ∃ R, DecoupledConsensusModel.Protocol.freezeRoot S.E
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) .g2) w).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) .g2) w).st.core.F
          S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) .g2)
          (late S.E S.hc (r + 1) .g2) = some R ∧ Block.Preceq P R := by
  apply clause_at_reader_of_carriersAbove S rho hexec.core P r hmajority
    .g2 (Or.inr rfl)
  · intro reader hreader hreaderHor hB
    exact ⟨honestRoundVoters_positive_at_g2_read_of_deadline
        S rho b0 b1 hexec P r hdeadline hcarriers hstableG2
          reader hreader hreaderHor hB,
      opposing_at_g2_read_subset_of_deadline
        S rho b0 b1 hexec P r hdeadline hcarriers hstableG2
          reader hreader hreaderHor hB⟩
  · exact hw
  · exact hhor

/-- The round-`r` G2 domain is strictly before the strict cut that realises the
round-`r` opening read. -/
private theorem rvt_g2_lt_opening_cut (S : Setup V) (r : Round) :
    domain S.E S.hc r .g2 < domain S.E S.hc r .g1 + 1 :=
  Int.lt_add_one_iff.mpr (q10_domain_g2_lt_domain_g1 S r).le

/-- That strict cut is still at or before the round action. -/
private theorem rvt_opening_cut_le_a (S : Setup V) (r : Round) :
    domain S.E S.hc r .g1 + 1 ≤ S.a r := by
  have he : S.a r = domain S.E S.hc r .g1 + 6 * S.E.Δ := by
    unfold Setup.a Protocol.HealConfig.a domain opening Phase.domainOffset
      Protocol.proposal_time Env.t slotStart
    ring
  have h : ∀ x d : Int, 0 < d → x + 1 ≤ x + 6 * d := by
    intro x d hd
    omega
  rw [he]
  exact h _ _ S.E.Δ_pos

/-- A strict G2 clause becomes the opening-read frame clause for that round. -/
theorem opening_sg_clause_of_g2_clause
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (P : Block V) (r : Round) (hr : 0 < r)
    (hG2 : ∀ w ∈ rho.honest,
      Block.Preceq P
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.F ∨
        ∃ raw, DecoupledConsensusModel.Protocol.freezeRoot S.E
            (NamedRun.stateBeforeTime S rho
              (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
            (NamedRun.stateBeforeTime S rho
              (domain S.E S.hc r .g2) w).st.core.F
            S.hc.η_SG r (early S.E S.hc r .g2) (late S.E S.hc r .g2) =
              some raw ∧ Block.Preceq P raw)
    (hK6opening : ∀ w ∈ rho.honest,
      Block.Preceq P
          (Protocol.get_fg_root
            (NamedRun.readAt S rho (domain S.E S.hc r .g1) w).st.core.toHealing.toFG) ∨
        P ∈ Internal.PhaseGrades.filteredTree
          (NamedRun.readAt S rho (domain S.E S.hc r .g1) w))
    (hhor : domain S.E S.hc r .g1 ≤ rho.horizon) :
    ∀ w ∈ rho.honest,
      let n := NamedRun.readAt S rho (domain S.E S.hc r .g1) w
      Block.Preceq P n.st.core.F ∨
        ∃ raw : Block V,
          (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g2 =
            some (some raw) ∧ Block.Preceq P raw := by
  intro w hw
  let t := domain S.E S.hc r .g1 + 1
  have hcut : domain S.E S.hc r .g2 < t := rvt_g2_lt_opening_cut S r
  have hta : t ≤ S.a r := rvt_opening_cut_le_a S r
  have hg2hor : domain S.E S.hc r .g2 ≤ rho.horizon :=
    (q10_domain_g2_lt_domain_g1 S r).le.trans hhor
  have hbridge : NamedRun.readAt S rho (domain S.E S.hc r .g1) w =
      NamedRun.stateBeforeTime S rho t w := by
    dsimp only [t]
    rw [readAt_eq_succ]
  rcases hG2 w hw with hPF | ⟨raw, hfreeze, hPraw⟩
  · left
    rw [hbridge]
    exact Block.preceq_trans hPF
      (incl_strict_F_mono S rho core.toNamedScheduleWellFormed w hcut.le)
  · by_cases hPF : Block.Preceq P
        (NamedRun.readAt S rho (domain S.E S.hc r .g1) w).st.core.F
    · exact Or.inl hPF
    · right
      have hcompat : Block.compatible P
          (NamedRun.readAt S rho (domain S.E S.hc r .g1) w).st.core.F = true := by
        rcases hK6opening w hw with hroot | hPtree
        · have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_readAt S rho
            (domain S.E S.hc r .g1) w
          have hFroot := Proofs.Records.preceq_get_fg_root_of_F
            (st := (NamedRun.readAt S rho (domain S.E S.hc r .g1) w).st.core.toHealing.toFG)
            (by simpa only [Protocol.Store.toHealing] using hFJ)
          exact Block.compatible_of_preceq_common hroot hFroot
        · simp only [Block.compatible, Bool.or_eq_true]
          exact Or.inr (q10_filtered_F hPtree)
      have hcomplete := FrameCompleted.frame_g2_completed S rho core w hw r hr t
        hcut hta hg2hor
      rw [hfreeze] at hcomplete
      rw [← hbridge] at hcomplete
      simp only [Option.map_some] at hcomplete
      exact ⟨_, hcomplete, clip_retains raw _ P hcompat hPraw⟩







/-- The votes-form seed produces the next post-outage certificate. K6 supplies
later G2-domain viability. FG-root compatibility protects stable writes. -/
theorem postOutageAbove_of_seed'
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (hforming : GradeFormingThroughout S rho)
    {r : Round}
    (hseed : HonestCarriersAbove S rho P r ∧
      ∀ w ∈ rho.honest, ∀ t,
        domain S.E S.hc r .g2 ≤ t → t ≤ domain S.E S.hc (r + 1) .g2 →
        Block.Preceq P
          (Protocol.get_stable (NamedRun.stateBeforeTime S rho t w).st.core))
    (hK6all : ∀ t, b0 ≤ t → t ≤ rho.horizon → ∀ u ∈ rho.honest,
      Block.Preceq P
          (Protocol.get_fg_root
            (NamedRun.readAt S rho t u).st.core.toHealing.toFG) ∨
        P ∈ Internal.PhaseGrades.filteredTree (NamedRun.readAt S rho t u))
    (hfg : ∀ w ∈ rho.honest, ∀ u,
      domain S.E S.hc (r + 1) .g2 ≤ u →
      u < domain S.E S.hc (r + 2) .g2 →
      u = Protocol.support_cutoff S.E (S.E.slotOf u) →
      Block.compatible P (Protocol.get_fg_root
        (NamedActionReads.confirmationReadAt S rho w u).st.core.toHealing.toFG) = true)
    (hpost : b1 ≤ S.a r)
    (hhor : domain S.E S.hc (r + 2) .g2 ≤ rho.horizon)
    : PostOutageAbove S rho P (r + 1) := by
  have hdomainHor : domain S.E S.hc (r + 1) .g2 ≤ rho.horizon :=
    (base_domain_g2_mono S (Nat.le_succ (r + 1))).trans hhor
  have hb0DeltaDomain2 : b0 + S.E.Δ ≤ domain S.E S.hc (r + 2) .g2 :=
    (Int.add_le_add_right (hexec.interval.2.1.trans hpost) S.E.Δ).trans
      ((action_delta_le_early S S.hc.R_ge_three
        (Nat.lt_add_of_pos_right (by omega : 0 < 2))).trans
          (early_le_domain S (r + 2)))
  have hDelta : (1 : Time) ≤ S.E.Δ := by
    simpa only [zero_add] using Int.add_one_le_iff.mpr S.E.Δ_pos
  have hb0SuccDomain2 : b0 + 1 ≤ domain S.E S.hc (r + 2) .g2 :=
    (Int.add_le_add_left hDelta b0).trans hb0DeltaDomain2
  have hb0Domain2Pred : b0 ≤ domain S.E S.hc (r + 2) .g2 - 1 := by
    exact Int.le_sub_one_iff.mpr (Int.add_one_le_iff.mp hb0SuccDomain2)
  have hdomain2PredHor : domain S.E S.hc (r + 2) .g2 - 1 ≤ rho.horizon := by
    exact (Int.sub_le_self _ (by norm_num)).trans hhor
  have hdomain2PredSucc : domain S.E S.hc (r + 2) .g2 - 1 + 1 =
      domain S.E S.hc (r + 2) .g2 := by
    ring
  have hviable2 : ∀ u ∈ rho.honest,
      Block.Preceq P
          (Protocol.get_fg_root
            (Proofs.HealingSurface.relativeG2Read S rho (r + 2) u).st.core.toHealing.toFG) ∨
        P ∈ Internal.PhaseGrades.filteredTree
          (Proofs.HealingSurface.relativeG2Read S rho (r + 2) u) := by
    intro u hu
    have hread := hK6all (domain S.E S.hc (r + 2) .g2 - 1)
      hb0Domain2Pred hdomain2PredHor u hu
    rw [readAt_eq_succ, hdomain2PredSucc] at hread
    simpa only [Proofs.HealingSurface.relativeG2Read, Internal.PhaseGrades.readAt] using hread
  have hmajority : GradeFormingMajority S rho (r + 1) :=
    hforming (r + 1) (Nat.succ_pos r)
      (Or.inr ⟨.g2, phase_domain_nonneg S (Nat.succ_pos r) (Or.inr rfl),
        hdomainHor⟩)
  have hG2 : ∀ w ∈ rho.honest, Block.Preceq P
      (postOutageReadAt S rho w (r + 1)).st.core.F ∨
        ∃ R, postOutageFrozenG2At S rho w (r + 1) = some R ∧
          Block.Preceq P R := by
    intro w hw
    simpa only [postOutageReadAt, postOutageFrozenG2At] using
      clauses_at_reader_of_carriersAbove_of_outageExecution
        S rho b0 b1 hexec P r hpost
        hseed.1 hseed.2 hmajority .g2 (Or.inr rfl)
        (fun hbad => False.elim (by cases hbad)) w hw
        hdomainHor
  have hstable : ∀ w ∈ rho.honest, ∀ t,
      domain S.E S.hc (r + 1) .g2 ≤ t →
      t ≤ domain S.E S.hc (r + 2) .g2 →
      Block.Preceq P
        (Protocol.get_stable (NamedRun.stateBeforeTime S rho t w).st.core) := by
    intro w hw t hlo hhi
    apply stable_above_P_through_succ_of_floor S P r hseed.2 hexec.core hw
      hviable2 t hlo hhi
    intro k u huLo huHi he hpos hcut G hG hlat
    have hbefore := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S
      hexec.core.toNamedScheduleWellFormed he
    change NamedRun.stateBefore S rho k w =
      NamedRun.stateBeforeTime S rho u w at hbefore
    have huHiStop : u < domain S.E S.hc (r + 2) .g2 := huHi.trans_le hhi
    have hread : NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBefore S rho k w) u =
        NamedActionReads.confirmationReadAt S rho w u := by
      rw [hbefore]
      rfl
    have hround := support_cutoff_round_of_domain_window S (r + 1) u
      huLo huHiStop hcut
    have ht := domain_g2_lt_support_cutoff_of_le S (r + 1) u huLo hcut
    have hta : u ≤ opening S.E S.hc (r + 2) := by
      exact huHiStop.le.trans (by
        rw [← domain_g1_eq_opening]
        exact (q10_domain_g2_lt_domain_g1 S (r + 2)).le)
    have hdomainHor : domain S.E S.hc (r + 1) .g2 ≤ rho.horizon :=
      (base_domain_g2_mono S (Nat.le_succ (r + 1))).trans hhor
    have hFstop : Block.Preceq
        (NamedRun.stateBeforeTime S rho u w).st.core.F
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 2) .g2) w).st.core.F :=
      incl_strict_F_mono S rho hexec.core.toNamedScheduleWellFormed w huHiStop.le
    have hcompat : Block.compatible P
        (NamedRun.stateBeforeTime S rho u w).st.core.F = true := by
      rcases hviable2 w hw with hroot | hPtree
      · have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
          S rho (domain S.E S.hc (r + 2) .g2) w
        have hFroot := Proofs.Records.preceq_get_fg_root_of_F
          (st := (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 2) .g2) w).st.core.toHealing.toFG)
          (by simpa only [Protocol.Store.toHealing] using hFJ)
        have hroot' : Block.Preceq P
            (Protocol.get_fg_root
              (NamedRun.stateBeforeTime S rho
                (domain S.E S.hc (r + 2) .g2) w).st.core.toHealing.toFG) := by
          simpa only [Proofs.HealingSurface.relativeG2Read,
            Internal.PhaseGrades.filteredTree] using hroot
        exact Block.compatible_of_preceq_common hroot'
          (Block.preceq_trans hFstop hFroot)
      · have hFleP := q10_filtered_F (by simpa only [Proofs.HealingSurface.relativeG2Read,
          Internal.PhaseGrades.filteredTree] using hPtree)
        simp only [Block.compatible, Bool.or_eq_true]
        exact Or.inr (Block.preceq_trans hFstop hFleP)
    have hlat' : Block.Preceq P
        (NamedRun.stateBeforeTime S rho u w).st.core.latest_stable := by
      simpa only [hbefore] using hlat
    have hstableU : Block.Preceq P
        (Protocol.get_stable (NamedRun.stateBeforeTime S rho u w).st.core) := by
      apply preceq_get_stable_of_cases _ (Or.inr hlat')
      exact hcompat
    have hG' : dutyStableRoot S
        (NamedActionReads.confirmationReadAt S rho w u) = some G := by
      rw [← hread]
      exact hG
    exact confirmationDutyRoot_above_of_postOutageG2 S rho P (r + 1)
      hexec.core w hw (Nat.succ_pos r) u hround ht hta hdomainHor
      (hG2 w hw) hstableU (hfg w hw u huLo huHiStop hcut) hG'
  have hG1 : ∀ w ∈ rho.honest, Block.Preceq P
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g1) w).st.core.F ∨
        ∃ R, postOutageFrozenG1At S rho w (r + 1) = some R ∧
          Block.Preceq P R := by
    intro w hw
    simpa only [postOutageFrozenG1At] using
      clauses_at_reader_of_carriersAbove_of_outageExecution
        S rho b0 b1 hexec P r hpost
        hseed.1 hseed.2 hmajority .g1 (Or.inl rfl)
        (fun _ w hw => hstable w hw _
          (q10_domain_g2_lt_domain_g1 S (r + 1)).le
          (domain_g1_le_next_domain_g2 S (r + 1))) w hw
        ((domain_g1_le_next_domain_g2 S (r + 1)).trans hhor)
  exact postOutageAbove_succ_of_chain S rho P r hG2 hG1 hstable

/-- The certificate-facing successor derives the votes-form seed and then
uses `postOutageAbove_of_seed'`. -/
theorem postOutageAbove_succ_concrete_of_outageExecution
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (hforming : GradeFormingThroughout S rho)
    {r : Round}
    (hK6 : ∀ u ∈ rho.honest,
      Block.Preceq P
          (Protocol.get_fg_root
            (NamedActionReads.actionReadAt S rho u r).st.core.toHealing.toFG) ∨
        P ∈ Protocol.get_filtered_block_tree
          (NamedActionReads.actionReadAt S rho u r).st.core.toHealing.toFG)
    (hK6all : ∀ t, b0 ≤ t → t ≤ rho.horizon → ∀ u ∈ rho.honest,
      Block.Preceq P
          (Protocol.get_fg_root
            (NamedRun.readAt S rho t u).st.core.toHealing.toFG) ∨
        P ∈ Internal.PhaseGrades.filteredTree (NamedRun.readAt S rho t u))
    (hfg : ∀ w ∈ rho.honest, ∀ u,
      domain S.E S.hc (r + 1) .g2 ≤ u →
      u < domain S.E S.hc (r + 2) .g2 →
      u = Protocol.support_cutoff S.E (S.E.slotOf u) →
      Block.compatible P (Protocol.get_fg_root
        (NamedActionReads.confirmationReadAt S rho w u).st.core.toHealing.toFG) = true)
    (hr : 0 < r) (hpost : b1 ≤ S.a r)
    (hhor : domain S.E S.hc (r + 2) .g2 ≤ rho.horizon)
    (h : PostOutageAbove S rho P r) :
    PostOutageAbove S rho P (r + 1) := by
  have hdomainHor : domain S.E S.hc (r + 1) .g2 ≤ rho.horizon :=
    (base_domain_g2_mono S (Nat.le_succ (r + 1))).trans hhor
  have hactionHor : S.a r ≤ rho.horizon :=
    (action_le_domain S S.hc.R_ge_three (Nat.lt_succ_self r)).trans
      hdomainHor
  have hcarriers := carriersAbove_of_postOutageAbove S rho P r hexec.core
    hr hactionHor h hK6
  exact postOutageAbove_of_seed' S rho b0 b1 P hexec hforming
    ⟨hcarriers, h.2.2⟩ hK6all hfg hpost hhor


/-- Induction from the votes-form seed. The horizon premise is local to the
certificate requested at each iteration. -/
theorem postOutageAbove_induction_from_seed'
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (P : Block V)
    (r0 : Round) (hexec : OutageExecution S rho b0 b1)
    (hforming : GradeFormingThroughout S rho)
    (hseed : HonestCarriersAbove S rho P r0 ∧
      ∀ w ∈ rho.honest, ∀ t,
        domain S.E S.hc r0 .g2 ≤ t → t ≤ domain S.E S.hc (r0 + 1) .g2 →
        Block.Preceq P
          (Protocol.get_stable (NamedRun.stateBeforeTime S rho t w).st.core))
    (hK6 : ∀ q, r0 ≤ q → ∀ u ∈ rho.honest,
        Block.Preceq P
            (Protocol.get_fg_root
              (NamedActionReads.actionReadAt S rho u q).st.core.toHealing.toFG) ∨
          P ∈ Protocol.get_filtered_block_tree
            (NamedActionReads.actionReadAt S rho u q).st.core.toHealing.toFG)
    (hK6all : ∀ t, b0 ≤ t → t ≤ rho.horizon → ∀ u ∈ rho.honest,
      Block.Preceq P
          (Protocol.get_fg_root
            (NamedRun.readAt S rho t u).st.core.toHealing.toFG) ∨
        P ∈ Internal.PhaseGrades.filteredTree (NamedRun.readAt S rho t u))
    (hfg : ∀ q, r0 ≤ q → ∀ w ∈ rho.honest, ∀ u,
      domain S.E S.hc (q + 1) .g2 ≤ u →
      u < domain S.E S.hc (q + 2) .g2 →
      u = Protocol.support_cutoff S.E (S.E.slotOf u) →
      Block.compatible P (Protocol.get_fg_root
        (NamedActionReads.confirmationReadAt S rho w u).st.core.toHealing.toFG) = true)
    (hpost : b1 ≤ S.a r0) :
    ∀ k, domain S.E S.hc (r0 + k + 2) .g2 ≤ rho.horizon →
      PostOutageAbove S rho P (r0 + k + 1) := by
  intro k
  induction k with
  | zero =>
      intro hhor
      simpa only [Nat.add_zero] using
        postOutageAbove_of_seed' S rho b0 b1 P hexec hforming hseed
          hK6all
          (hfg r0 le_rfl) hpost (by simpa only [Nat.add_zero] using hhor)
  | succ k ih =>
      intro hhor
      have hprevHor : domain S.E S.hc (r0 + k + 2) .g2 ≤ rho.horizon :=
        (base_domain_g2_mono S (Nat.le_succ (r0 + k + 2))).trans
          (by simpa only [Nat.add_assoc] using hhor)
      have hprev := ih hprevHor
      have hr0q : r0 ≤ r0 + k + 1 := Nat.le_add_right r0 (k + 1)
      have hpostq : b1 ≤ S.a (r0 + k + 1) :=
        hpost.trans (Assembly.a_mono S hr0q)
      have hnext := postOutageAbove_succ_concrete_of_outageExecution
        S rho b0 b1 P hexec
        hforming (hK6 (r0 + k + 1) hr0q) hK6all
        (hfg (r0 + k + 1) hr0q) (Nat.succ_pos _) hpostq
        (by simpa only [Nat.add_assoc] using hhor) hprev
      simpa only [Nat.add_assoc] using hnext

/-- The two raw-root clauses needed at reads in one post-outage round. -/
def PostOutageRootsAbove (S : Setup V) (rho : NamedRun V) (P : Block V)
    (r : Round) : Prop :=
  (∀ w ∈ rho.honest,
      Block.Preceq P (postOutageReadAt S rho w r).st.core.F ∨
        ∃ R, postOutageFrozenG2At S rho w r = some R ∧ Block.Preceq P R) ∧
  (∀ w ∈ rho.honest, Block.Preceq P
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st.core.F ∨
        ∃ R, postOutageFrozenG1At S rho w r = some R ∧ Block.Preceq P R)

/-- A terminal-round certificate. The stable interval is clipped at the run
horizon, while both raw-root reads remain inside the horizon. -/
def PostOutageAboveTruncated (S : Setup V) (rho : NamedRun V) (P : Block V)
    (r : Round) : Prop :=
  PostOutageRootsAbove S rho P r ∧
    ∀ w ∈ rho.honest, ∀ t,
      domain S.E S.hc r .g2 ≤ t → t ≤ domain S.E S.hc (r + 1) .g2 →
      t ≤ rho.horizon →
      Block.Preceq P
        (Protocol.get_stable (NamedRun.stateBeforeTime S rho t w).st.core)

theorem PostOutageAbove.roots {S : Setup V} {rho : NamedRun V} {P : Block V}
    {r : Round} (h : PostOutageAbove S rho P r) :
    PostOutageRootsAbove S rho P r :=
  ⟨h.1, h.2.1⟩

theorem PostOutageAbove.truncated {S : Setup V} {rho : NamedRun V}
    {P : Block V} {r : Round} (h : PostOutageAbove S rho P r) :
    PostOutageAboveTruncated S rho P r :=
  ⟨h.roots, fun w hw t hlo hhi _ => h.2.2 w hw t hlo hhi⟩

private theorem confirmationDutyRoot_covers_core
    (S : Setup V) (rho : NamedRun V) (P : Block V) (q : Round)
    (core : NamedAdmissibleCore S rho) (w : V) (hw : w ∈ rho.honest)
    (hq : 0 < q) (u : Time) (hround : S.hc.round_of (S.E.slotOf u) = q)
    (ht : domain S.E S.hc q .g2 < u) (hta : u ≤ opening S.E S.hc (q + 1))
    (hhor : domain S.E S.hc q .g2 ≤ rho.horizon)
    (hroot : Block.Preceq P
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g2) w).st.core.F ∨
      ∃ R, postOutageFrozenG2At S rho w q = some R ∧ Block.Preceq P R)
    (hK6 : Block.Preceq P
        (Protocol.get_fg_root
          (NamedRun.stateBeforeTime S rho u w).st.core.toHealing.toFG) ∨
      P ∈ Protocol.get_filtered_block_tree
        (NamedRun.stateBeforeTime S rho u w).st.core.toHealing.toFG)
    {G : Block V}
    (hG : dutyStableRoot S (NamedActionReads.confirmationReadAt S rho w u) = some G) :
    Block.Preceq P G := by
  let n := NamedActionReads.confirmationReadAt S rho w u
  rcases hK6 with hfg | hPtree
  · have hfg' : Block.Preceq P (Protocol.get_fg_root n.st.core.toHealing.toFG) := by
      simpa only [n, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom] using hfg
    exact Block.preceq_trans hfg' (fgRoot_preceq_dutyStableRoot S n hG)
  rcases hroot with hPF | ⟨raw, hfreeze, hPraw⟩
  · have hPFnow : Block.Preceq P
        (NamedRun.stateBeforeTime S rho u w).st.core.F :=
      Block.preceq_trans hPF
        (incl_strict_F_mono S rho core.toNamedScheduleWellFormed w ht.le)
    have hFJ : Block.preceq n.st.core.F n.st.core.J = true := by
      change Block.preceq
        (NamedRun.stateBeforeTime S rho u w).st.core.F
        (NamedRun.stateBeforeTime S rho u w).st.core.J = true
      exact Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho u w
    have hFroot : Block.Preceq n.st.core.F
        (Protocol.get_fg_root n.st.core.toHealing.toFG) :=
      Proofs.Records.preceq_get_fg_root_of_F (st := n.st.core.toHealing.toFG)
        (by simpa only [Protocol.Store.toHealing] using hFJ)
    have hPFn : Block.Preceq P n.st.core.F := by
      simpa only [n, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom] using hPFnow
    exact Block.preceq_trans hPFn
      (Block.preceq_trans hFroot (fgRoot_preceq_dutyStableRoot S n hG))
  · have hFleP : Block.Preceq
        (NamedRun.stateBeforeTime S rho u w).st.core.F P := by
      have hf := q10_filtered_F hPtree
      simpa only [Protocol.Store.toHealing] using hf
    have hcompat : Block.compatible P
        (NamedRun.stateBeforeTime S rho u w).st.core.F = true := by
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr hFleP
    have hclip : Block.Preceq P
        (DecoupledConsensusModel.Protocol.clipGrade raw
          (NamedRun.stateBeforeTime S rho u w).st.core.F) :=
      (q10_retained_prefix raw
        (NamedRun.stateBeforeTime S rho u w).st.core.F P hcompat).mpr hPraw
    have hfreeze' : DecoupledConsensusModel.Protocol.freezeRoot S.E
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc q .g2) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc q .g2) w).st.core.F S.hc.η_SG q
        (early S.E S.hc q .g2) (late S.E S.hc q .g2) = some raw := by
      simpa only [postOutageFrozenG2At, postOutageReadAt,
        Proofs.HealingSurface.relativeG2Read, Internal.PhaseGrades.readAt] using hfreeze
    have hbase := FrameCompleted.frame_g2_completed_in_round
      S rho core w hw q hq u ht hta hhor
    have hframe := frame_phase_prepared_eq S rho w q .g2 u hround _ hbase
    rw [hfreeze'] at hframe
    have hnround : S.hc.round_of n.st.core.s = q := by
      simpa only [n, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom] using hround
    have hframe' : (DecoupledConsensusModel.Protocol.readFrame n.cache
        n.st.core.toHealing q).g2 =
        some (some (DecoupledConsensusModel.Protocol.clipGrade raw
          (NamedRun.stateBeforeTime S rho u w).st.core.F)) := by
      simpa only [n, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom] using hframe
    have hPtreeN : P ∈ Protocol.get_filtered_block_tree
        n.st.core.toHealing.toFG := by
      dsimp only [n]
      change P ∈ Protocol.get_filtered_block_tree
        (NamedRun.stateBeforeTime S rho u w).st.core.toHealing.toFG
      exact hPtree
    have hg2read : (readFrameAt S n).g2 =
        some (some (DecoupledConsensusModel.Protocol.clipGrade raw
          (NamedRun.stateBeforeTime S rho u w).st.core.F)) := by
      change (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing
        (S.hc.round_of n.st.core.s)).g2 = _
      rw [hnround]
      exact hframe'
    obtain ⟨A, hA, hPA⟩ := activeG2_covers S n hg2read hPtreeN (by
      simpa only [n, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom] using hclip)
    rw [dutyStableRoot_eq_activeG2, hA] at hG
    exact Option.some.inj hG ▸ hPA

/-- Stable output persists from one G2 domain through any in-horizon point of
that round. The exact-read K6 premise supplies the finalized-prefix guard for
each confirmation write and for the endpoint. -/
theorem stable_above_P_through_horizon_of_root
    (S : Setup V) (rho : NamedRun V) (b0 : Time) (P : Block V) (q : Round)
    (core : NamedAdmissibleCore S rho)
    (hroot : ∀ w ∈ rho.honest, Block.Preceq P
      (postOutageReadAt S rho w q).st.core.F ∨
        ∃ R, postOutageFrozenG2At S rho w q = some R ∧ Block.Preceq P R)
    (hstart : ∀ w ∈ rho.honest, Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc q .g2) w).st.core))
    (hK6all : ∀ t, b0 ≤ t → t ≤ rho.horizon → ∀ u ∈ rho.honest,
      Block.Preceq P
          (Protocol.get_fg_root
            (NamedRun.readAt S rho t u).st.core.toHealing.toFG) ∨
        P ∈ Internal.PhaseGrades.filteredTree (NamedRun.readAt S rho t u))
    (hq : 0 < q) (hb0start : b0 < domain S.E S.hc q .g2)
    (hstartHor : domain S.E S.hc q .g2 ≤ rho.horizon)
    (w : V) (hw : w ∈ rho.honest) (t : Time)
    (hlo : domain S.E S.hc q .g2 ≤ t)
    (hhi : t ≤ domain S.E S.hc (q + 1) .g2) (hhor : t ≤ rho.horizon) :
    Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho t w).st.core) := by
  let start := domain S.E S.hc q .g2
  let i := (rho.events.filter (fun e => decide (e.time < start))).length
  let j := (rho.events.filter (fun e => decide (e.time < t))).length
  have hi : NamedRun.stateBeforeTime S rho start w =
      NamedRun.stateBefore S rho i w :=
    congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S
      core.toNamedScheduleWellFormed start) w
  have hj : NamedRun.stateBeforeTime S rho t w =
      NamedRun.stateBefore S rho j w :=
    congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S
      core.toNamedScheduleWellFormed t) w
  have hij : i ≤ j := by
    dsimp only [i, j, start]
    exact strict_lengths_mono rho hlo
  have hhold : Block.Preceq P (NamedRun.stateBefore S rho i w).st.core.F ∨
      Block.Preceq P (NamedRun.stateBefore S rho i w).st.core.latest_stable := by
    rw [← hi]
    have hs := hstart w hw
    dsimp only [start] at hs ⊢
    unfold Protocol.get_stable at hs
    split at hs
    · exact Or.inr hs
    · exact Or.inl hs
  have hcases := stateBefore_stable_covered_of_comparable S rho w i j hij hhold
    (fun k u hik hkj he hpos hcut G hG _ => by
      have huStart : start ≤ u := Proofs.Optimistic.le_time_of_index_ge S
        core.toNamedScheduleWellFormed (t := start) (j := k) hik he
      have huT : u < t := by
        have hins := Proofs.Optimistic.filter_true_of_index_lt S
          core.toNamedScheduleWellFormed (fun e => decide (e.time < t))
          (Proofs.Optimistic.downward_lt t) hkj he
        simpa only [decide_eq_true_eq, NamedEvent.time] using hins
      have hu0 : (0 : Time) ≤ u :=
        (phase_domain_nonneg S hq (Or.inr rfl)).trans
          (by simpa only [start] using huStart)
      have hb0u : b0 < u := hb0start.trans_le (by
        simpa only [start] using huStart)
      have hb0pred : b0 ≤ u - 1 := Int.le_sub_one_iff.mpr hb0u
      have hupred : u - 1 ≤ rho.horizon :=
        (Int.sub_le_self u (by norm_num)).trans (huT.le.trans hhor)
      have hmem := hK6all (u - 1) hb0pred hupred w hw
      have hpredSucc : u - 1 + 1 = u := by ring
      rw [readAt_eq_succ, hpredSucc] at hmem
      have hbefore := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S
        core.toNamedScheduleWellFormed he
      change NamedRun.stateBefore S rho k w =
        NamedRun.stateBeforeTime S rho u w at hbefore
      have hread : NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S rho k w) u =
          NamedActionReads.confirmationReadAt S rho w u := by
        rw [hbefore]
        rfl
      have hG' : dutyStableRoot S
          (NamedActionReads.confirmationReadAt S rho w u) = some G := by
        rw [← hread]
        exact hG
      have hround := support_cutoff_round_of_domain_window S q u
        (by simpa only [start] using huStart)
        (huT.trans_le hhi) hcut
      have ht := domain_g2_lt_support_cutoff_of_le S q u
        (by simpa only [start] using huStart) hcut
      have hta : u ≤ opening S.E S.hc (q + 1) :=
        (huT.trans_le hhi).le.trans (by
          rw [← domain_g1_eq_opening]
          exact (q10_domain_g2_lt_domain_g1 S (q + 1)).le)
      exact Or.inl (confirmationDutyRoot_covers_core S rho P q core w hw hq u
        hround ht hta hstartHor (hroot w hw) hmem hG'))
  have hb0t : b0 < t := hb0start.trans_le hlo
  have hb0pred : b0 ≤ t - 1 := Int.le_sub_one_iff.mpr hb0t
  have hpredHor : t - 1 ≤ rho.horizon :=
    (Int.sub_le_self t (by norm_num)).trans hhor
  have hPtree := hK6all (t - 1) hb0pred hpredHor w hw
  have hpredSucc : t - 1 + 1 = t := by ring
  rw [readAt_eq_succ, hpredSucc] at hPtree
  have hcompat : Block.compatible P
      (NamedRun.stateBeforeTime S rho t w).st.core.F = true := by
    rcases hPtree with hroot | hPtree
    · have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        S rho t w
      have hFroot := Proofs.Records.preceq_get_fg_root_of_F
        (st := (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.toFG)
        (by simpa only [Protocol.Store.toHealing] using hFJ)
      exact Block.compatible_of_preceq_common hroot hFroot
    · simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr (q10_filtered_F hPtree)
  rw [hj]
  rw [hj] at hcompat
  rcases hcases with hF | hstable
  · unfold Protocol.get_stable
    split
    · exact Block.preceq_trans hF (by assumption)
    · exact hF
  · exact preceq_get_stable _ hstable hcompat

/-- The successor certificate with its stable interval clipped at the run
horizon. Only the successor's G1 domain read must be in the run. -/
theorem postOutageAbove_of_seed_truncated
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (hforming : GradeFormingThroughout S rho)
    {r : Round}
    (hseed : HonestCarriersAbove S rho P r ∧
      ∀ w ∈ rho.honest, ∀ t,
        domain S.E S.hc r .g2 ≤ t → t ≤ domain S.E S.hc (r + 1) .g2 →
        Block.Preceq P
          (Protocol.get_stable (NamedRun.stateBeforeTime S rho t w).st.core))
    (hK6all : ∀ t, b0 ≤ t → t ≤ rho.horizon → ∀ u ∈ rho.honest,
      Block.Preceq P
          (Protocol.get_fg_root
            (NamedRun.readAt S rho t u).st.core.toHealing.toFG) ∨
        P ∈ Internal.PhaseGrades.filteredTree (NamedRun.readAt S rho t u))
    (hpost : b1 ≤ S.a r)
    (hhor : domain S.E S.hc (r + 1) .g1 ≤ rho.horizon) :
    PostOutageAboveTruncated S rho P (r + 1) := by
  have hdomainHor : domain S.E S.hc (r + 1) .g2 ≤ rho.horizon :=
    (q10_domain_g2_lt_domain_g1 S (r + 1)).le.trans hhor
  have hb0DeltaDomain : b0 + S.E.Δ ≤ domain S.E S.hc (r + 1) .g2 :=
    (Int.add_le_add_right (hexec.interval.2.1.trans hpost) S.E.Δ).trans
      ((action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r)).trans
        (early_le_domain S (r + 1)))
  have hb0Domain : b0 < domain S.E S.hc (r + 1) .g2 :=
    (lt_add_of_pos_right b0 S.E.Δ_pos).trans_le hb0DeltaDomain
  have hmajority : GradeFormingMajority S rho (r + 1) :=
    hforming (r + 1) (Nat.succ_pos r)
      (Or.inr ⟨.g2, phase_domain_nonneg S (Nat.succ_pos r) (Or.inr rfl),
        hdomainHor⟩)
  have hG2 : ∀ w ∈ rho.honest, Block.Preceq P
      (postOutageReadAt S rho w (r + 1)).st.core.F ∨
        ∃ R, postOutageFrozenG2At S rho w (r + 1) = some R ∧
          Block.Preceq P R := by
    intro w hw
    simpa only [postOutageReadAt, postOutageFrozenG2At] using
      clauses_at_reader_of_carriersAbove_of_outageExecution
        S rho b0 b1 hexec P r hpost
        hseed.1 hseed.2 hmajority .g2 (Or.inr rfl)
        (fun hbad => False.elim (by cases hbad)) w hw hdomainHor
  have hstart : ∀ w ∈ rho.honest, Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core) := by
    intro w hw
    exact hseed.2 w hw _ (base_domain_g2_mono S (Nat.le_succ r)) le_rfl
  have hstable : ∀ w ∈ rho.honest, ∀ t,
      domain S.E S.hc (r + 1) .g2 ≤ t →
      t ≤ domain S.E S.hc (r + 2) .g2 → t ≤ rho.horizon →
      Block.Preceq P
        (Protocol.get_stable (NamedRun.stateBeforeTime S rho t w).st.core) := by
    intro w hw t hlo hhi htHor
    exact stable_above_P_through_horizon_of_root S rho b0 P (r + 1)
      hexec.core hG2 hstart hK6all (Nat.succ_pos r) hb0Domain
      hdomainHor w hw t hlo hhi htHor
  have hG1 : ∀ w ∈ rho.honest, Block.Preceq P
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g1) w).st.core.F ∨
        ∃ R, postOutageFrozenG1At S rho w (r + 1) = some R ∧
          Block.Preceq P R := by
    intro w hw
    simpa only [postOutageFrozenG1At] using
      clauses_at_reader_of_carriersAbove_of_outageExecution
        S rho b0 b1 hexec P r hpost
        hseed.1 hseed.2 hmajority .g1 (Or.inl rfl)
        (fun _ w hw => hstable w hw _
          (q10_domain_g2_lt_domain_g1 S (r + 1)).le
          (domain_g1_le_next_domain_g2 S (r + 1)) hhor) w hw hhor
  exact ⟨⟨hG2, hG1⟩, hstable⟩

/-- Every successor round whose G1 domain read is in the horizon has a
terminal certificate. Earlier rounds are produced by the full induction;
the last partial round uses the clipped successor above. -/
theorem postOutageAbove_induction_through_horizon_from_seed_of_outageExecution'
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (P : Block V)
    (r0 : Round) (hexec : OutageExecution S rho b0 b1)
    (hforming : GradeFormingThroughout S rho)
    (hseed : HonestCarriersAbove S rho P r0 ∧
      ∀ w ∈ rho.honest, ∀ t,
        domain S.E S.hc r0 .g2 ≤ t → t ≤ domain S.E S.hc (r0 + 1) .g2 →
        Block.Preceq P
          (Protocol.get_stable (NamedRun.stateBeforeTime S rho t w).st.core))
    (hK6 : ∀ q, r0 ≤ q → ∀ u ∈ rho.honest,
      Block.Preceq P
          (Protocol.get_fg_root
            (NamedActionReads.actionReadAt S rho u q).st.core.toHealing.toFG) ∨
        P ∈ Protocol.get_filtered_block_tree
          (NamedActionReads.actionReadAt S rho u q).st.core.toHealing.toFG)
    (hK6all : ∀ t, b0 ≤ t → t ≤ rho.horizon → ∀ u ∈ rho.honest,
      Block.Preceq P
          (Protocol.get_fg_root
            (NamedRun.readAt S rho t u).st.core.toHealing.toFG) ∨
        P ∈ Internal.PhaseGrades.filteredTree (NamedRun.readAt S rho t u))
    (hfg : ∀ q, r0 ≤ q → ∀ w ∈ rho.honest, ∀ u,
      domain S.E S.hc (q + 1) .g2 ≤ u →
      u < domain S.E S.hc (q + 2) .g2 →
      u = Protocol.support_cutoff S.E (S.E.slotOf u) →
      Block.compatible P (Protocol.get_fg_root
        (NamedActionReads.confirmationReadAt S rho w u).st.core.toHealing.toFG) = true)
    (hpost : b1 ≤ S.a r0) :
    ∀ k, domain S.E S.hc (r0 + k + 1) .g1 ≤ rho.horizon →
      PostOutageAboveTruncated S rho P (r0 + k + 1) := by
  intro k hhor
  cases k with
  | zero =>
      simpa only [Nat.add_zero] using
        postOutageAbove_of_seed_truncated S rho b0 b1 P hexec hforming
          hseed hK6all hpost (by simpa only [Nat.add_zero] using hhor)
  | succ k =>
      have hprevHor : domain S.E S.hc (r0 + k + 2) .g2 ≤ rho.horizon :=
        (q10_domain_g2_lt_domain_g1 S (r0 + k + 2)).le.trans
          (by simpa only [Nat.add_assoc] using hhor)
      have hprev := postOutageAbove_induction_from_seed' S rho b0 b1 P r0
        hexec hforming hseed hK6 hK6all hfg hpost k
        (by simpa only [Nat.add_assoc] using hprevHor)
      have hr0q : r0 ≤ r0 + k + 1 := Nat.le_add_right r0 (k + 1)
      have hpostq : b1 ≤ S.a (r0 + k + 1) :=
        hpost.trans (Assembly.a_mono S hr0q)
      have hcarriers := carriersAbove_of_postOutageAbove S rho P
        (r0 + k + 1) hexec.core (Nat.succ_pos _)
        ((action_le_domain S S.hc.R_ge_three (Nat.lt_succ_self _)).trans
          hprevHor) hprev (hK6 (r0 + k + 1) hr0q)
      have hnext := postOutageAbove_of_seed_truncated S rho b0 b1 P hexec
        hforming ⟨hcarriers, hprev.2.2⟩ hK6all hpostq
        (by simpa only [Nat.add_assoc] using hhor)
      simpa only [Nat.add_assoc] using hnext

/-- The exact post-outage seed consumed by the certificate induction: honest
carriers cover `P` in the seed round, and the stable output covers `P` through
that round's complete G2-domain interval. -/
def PostOutageSeedAt (S : Setup V) (rho : NamedRun V) (P : Block V)
    (r : Round) : Prop :=
  HonestCarriersAbove S rho P r ∧
    ∀ w ∈ rho.honest, ∀ t,
      domain S.E S.hc r .g2 ≤ t →
      t ≤ domain S.E S.hc (r + 1) .g2 →
      Block.Preceq P
        (Protocol.get_stable (NamedRun.stateBeforeTime S rho t w).st.core)

/-- An opening SG clause, its action carriers, and the stable value at the G2
domain produce the exact seed. All later stable writes are protected by K6. -/
theorem postOutageSeedAt_of_sg_clause
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (Pn : NamedBlock V) (r : Round)
    (hexec : OutageExecution S rho b0 b1) (hr : 0 < r)
    (hsg : ∀ w ∈ rho.honest,
      let n := NamedRun.readAt S rho (domain S.E S.hc r .g1) w
      Block.Preceq Pn.erase n.st.core.F ∨
        ∃ raw : Block V,
          (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g2 =
            some (some raw) ∧ Block.Preceq Pn.erase raw)
    (hcarriers : HonestCarriersAbove S rho Pn.erase r)
    (hstart : ∀ w ∈ rho.honest, Block.Preceq Pn.erase
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc r .g2) w).st.core))
    (hK6all : ∀ t, b0 ≤ t → t ≤ rho.horizon → ∀ u ∈ rho.honest,
      Block.Preceq Pn.erase
          (Protocol.get_fg_root
            (NamedRun.readAt S rho t u).st.core.toHealing.toFG) ∨
        Pn.erase ∈ Internal.PhaseGrades.filteredTree (NamedRun.readAt S rho t u))
    (hb0start : b0 < domain S.E S.hc r .g2)
    (hnextHor : domain S.E S.hc (r + 1) .g2 ≤ rho.horizon) :
    PostOutageSeedAt S rho Pn.erase r := by
  refine ⟨hcarriers, ?_⟩
  intro w hw t hlo hhi
  let start := domain S.E S.hc r .g2
  let i := (rho.events.filter (fun e => decide (e.time < start))).length
  let j := (rho.events.filter (fun e => decide (e.time < t))).length
  have hi : NamedRun.stateBeforeTime S rho start w =
      NamedRun.stateBefore S rho i w :=
    congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S
      hexec.core.toNamedScheduleWellFormed start) w
  have hj : NamedRun.stateBeforeTime S rho t w =
      NamedRun.stateBefore S rho j w :=
    congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S
      hexec.core.toNamedScheduleWellFormed t) w
  have hij : i ≤ j := by
    dsimp only [i, j, start]
    exact strict_lengths_mono rho hlo
  have hhold : Block.Preceq Pn.erase
        (NamedRun.stateBefore S rho i w).st.core.F ∨
      Block.Preceq Pn.erase
        (NamedRun.stateBefore S rho i w).st.core.latest_stable := by
    rw [← hi]
    have hs := hstart w hw
    dsimp only [start] at hs ⊢
    unfold Protocol.get_stable at hs
    split at hs
    · exact Or.inr hs
    · exact Or.inl hs
  have hnextPred : b0 ≤ domain S.E S.hc (r + 1) .g2 - 1 := by
    apply Int.le_sub_one_iff.mpr
    exact hb0start.trans_le (base_domain_g2_mono S (Nat.le_succ r))
  have hnextPredHor : domain S.E S.hc (r + 1) .g2 - 1 ≤ rho.horizon :=
    (Int.sub_le_self _ (by norm_num)).trans hnextHor
  have hnextSucc : domain S.E S.hc (r + 1) .g2 - 1 + 1 =
      domain S.E S.hc (r + 1) .g2 := by ring
  have hK6next : ∀ reader ∈ rho.honest,
      Block.Preceq Pn.erase
          (Protocol.get_fg_root
            (Proofs.HealingSurface.relativeG2Read S rho (r + 1) reader).st.core.toHealing.toFG) ∨
        Pn.erase ∈ Internal.PhaseGrades.filteredTree
          (Proofs.HealingSurface.relativeG2Read S rho (r + 1) reader) := by
    intro reader hreader
    have hm := hK6all (domain S.E S.hc (r + 1) .g2 - 1)
      hnextPred hnextPredHor reader hreader
    rw [readAt_eq_succ, hnextSucc] at hm
    simpa only [Proofs.HealingSurface.relativeG2Read,
      Internal.PhaseGrades.readAt] using hm
  have hcases := stateBefore_stable_covered_of_comparable S rho w i j hij hhold
    (fun k u hik hkj he hpos hcut G hG _ => by
      have huStart : start ≤ u := Proofs.Optimistic.le_time_of_index_ge S
        hexec.core.toNamedScheduleWellFormed (t := start) (j := k) hik he
      have huT : u < t := by
        have hins := Proofs.Optimistic.filter_true_of_index_lt S
          hexec.core.toNamedScheduleWellFormed (fun e => decide (e.time < t))
          (Proofs.Optimistic.downward_lt t) hkj he
        simpa only [decide_eq_true_eq, NamedEvent.time] using hins
      have huNext : u < domain S.E S.hc (r + 1) .g2 := huT.trans_le hhi
      have hbefore := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S
        hexec.core.toNamedScheduleWellFormed he
      change NamedRun.stateBefore S rho k w =
        NamedRun.stateBeforeTime S rho u w at hbefore
      have hread : NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S rho k w) u =
          NamedActionReads.confirmationReadAt S rho w u := by
        rw [hbefore]
        rfl
      have hG' : dutyStableRoot S
          (NamedActionReads.confirmationReadAt S rho w u) = some G := by
        rw [← hread]
        exact hG
      have hb0u : b0 < u := hb0start.trans_le (by
        simpa only [start] using huStart)
      have hb0pred : b0 ≤ u - 1 := Int.le_sub_one_iff.mpr hb0u
      have hupred : u - 1 ≤ rho.horizon :=
        (Int.sub_le_self u (by norm_num)).trans
          (huT.le.trans (hhi.trans hnextHor))
      have hmem := hK6all (u - 1) hb0pred hupred w hw
      have hpredSucc : u - 1 + 1 = u := by ring
      rw [readAt_eq_succ, hpredSucc] at hmem
      have hfg : Block.compatible Pn.erase
          (Protocol.get_fg_root
            (NamedActionReads.confirmationReadAt S rho w u).st.core.toHealing.toFG) =
            true := by
        rcases hmem with hroot | htree
        · simp only [Block.compatible, Bool.or_eq_true]
          left
          simpa only [NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom] using hroot
        · have hfgPre := Proofs.Records.preceq_get_fg_root_of_mem_filtered htree
          simp only [Block.compatible, Bool.or_eq_true]
          right
          simpa only [NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom] using hfgPre
      exact confirmationDutyRoot_comparable_of_sg_clause S rho b0 b1 Pn r
        hexec hr hsg w hw u (by simpa only [start] using huStart) huNext
          hcut (hK6next w hw) hfg hG')
  have hb0t : b0 < t := hb0start.trans_le hlo
  have hb0pred : b0 ≤ t - 1 := Int.le_sub_one_iff.mpr hb0t
  have hpredHor : t - 1 ≤ rho.horizon :=
    (Int.sub_le_self t (by norm_num)).trans (hhi.trans hnextHor)
  have hPtree := hK6all (t - 1) hb0pred hpredHor w hw
  have hpredSucc : t - 1 + 1 = t := by ring
  rw [readAt_eq_succ, hpredSucc] at hPtree
  have hcompat : Block.compatible Pn.erase
      (NamedRun.stateBeforeTime S rho t w).st.core.F = true := by
    rcases hPtree with hroot | htree
    · have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        S rho t w
      have hFroot := Proofs.Records.preceq_get_fg_root_of_F
        (st := (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.toFG)
        (by simpa only [Protocol.Store.toHealing] using hFJ)
      exact Block.compatible_of_preceq_common hroot hFroot
    · simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr (q10_filtered_F htree)
  rw [hj]
  rw [hj] at hcompat
  exact preceq_get_stable_of_cases _ hcases hcompat


/-- Once the exact seed survives the transition, every strictly later
horizon-local round has a truncated post-outage certificate. -/
theorem postOutageAboveTruncated_after_transition
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (P : Block V)
    (r0 : Round) (hexec : OutageExecution S rho b0 b1)
    (hforming : GradeFormingThroughout S rho)
    (hseed : PostOutageSeedAt S rho P r0)
    (hK6 : ∀ q, r0 ≤ q → ∀ u ∈ rho.honest,
      Block.Preceq P
          (Protocol.get_fg_root
            (NamedActionReads.actionReadAt S rho u q).st.core.toHealing.toFG) ∨
        P ∈ Protocol.get_filtered_block_tree
          (NamedActionReads.actionReadAt S rho u q).st.core.toHealing.toFG)
    (hK6all : ∀ t, b0 ≤ t → t ≤ rho.horizon → ∀ u ∈ rho.honest,
      Block.Preceq P
          (Protocol.get_fg_root
            (NamedRun.readAt S rho t u).st.core.toHealing.toFG) ∨
        P ∈ Internal.PhaseGrades.filteredTree (NamedRun.readAt S rho t u))
    (hfg : ∀ q, r0 ≤ q → ∀ w ∈ rho.honest, ∀ u,
      domain S.E S.hc (q + 1) .g2 ≤ u →
      u < domain S.E S.hc (q + 2) .g2 →
      u = Protocol.support_cutoff S.E (S.E.slotOf u) →
      Block.compatible P (Protocol.get_fg_root
        (NamedActionReads.confirmationReadAt S rho w u).st.core.toHealing.toFG) = true)
    (hpost : b1 ≤ S.a r0) :
    ∀ q, r0 < q → domain S.E S.hc q .g1 ≤ rho.horizon →
      PostOutageAboveTruncated S rho P q := by
  intro q hr0q hqHor
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_iff.mpr hr0q)
  rw [Nat.succ_add] at hk
  have hq : q = r0 + k + 1 := by
    simpa only [Nat.succ_eq_add_one] using hk
  subst q
  have hcert :=
    postOutageAbove_induction_through_horizon_from_seed_of_outageExecution'
      S rho b0 b1 P r0 hexec hforming hseed hK6 hK6all hfg hpost k
  exact hcert hqHor


theorem output_floors_at_read
    (S : Setup V) (rho : NamedRun V) (P : Block V) (q : Round)
    (core : NamedAdmissibleCore S rho) (h : PostOutageRootsAbove S rho P q)
    (w : V) (hw : w ∈ rho.honest) (t : Time) (ht0 : 0 ≤ t)
    (hq : 0 < q) (hopen : opening S.E S.hc q ≤ t)
    (hnext : t < opening S.E S.hc (q + 1)) (hhor : t ≤ rho.horizon)
    (hK6 : Block.Preceq P
        (Protocol.get_fg_root
          (NamedRun.readAt S rho t w).st.core.toHealing.toFG) ∨
      P ∈ Protocol.get_filtered_block_tree
        (NamedRun.readAt S rho t w).st.core.toHealing.toFG) :
    (∀ G, activeG2 S (NamedRun.readAt S rho t w) = some G → Block.Preceq P G) ∧
      Block.Preceq P (sgRoot S (NamedRun.readAt S rho t w)) := by
  rcases hK6 with hroot | hPtree
  · refine ⟨?_, ?_⟩
    · intro G hG
      exact preceq_activeG2_of_preceq_fg_root S
        (NamedRun.readAt S rho t w) hroot hG
    · exact preceq_sgRoot_of_fg_root S (NamedRun.readAt S rho t w) hroot
  have hsucc : t + 1 ≤ opening S.E S.hc (q + 1) := Int.add_one_le_iff.mpr hnext
  have htt1 : t < t + 1 := Int.lt_add_one_iff.mpr le_rfl
  have htt1le : t ≤ t + 1 := htt1.le
  have hg2lt : domain S.E S.hc q .g2 < t + 1 :=
    lt_of_le_of_lt ((domain_le_opening S q).trans hopen) htt1
  have hg1lt : domain S.E S.hc q .g1 < t + 1 := by
    rw [domain_g1_eq_opening]
    exact lt_of_le_of_lt hopen htt1
  have hg2hor : domain S.E S.hc q .g2 ≤ rho.horizon :=
    (domain_le_opening S q).trans (hopen.trans hhor)
  have hg1hor : domain S.E S.hc q .g1 ≤ rho.horizon := by
    rw [domain_g1_eq_opening]
    exact hopen.trans hhor
  have hFleP : Block.Preceq
      (NamedRun.stateBeforeTime S rho (t + 1) w).st.core.F P := by
    have hfloor := q10_filtered_F hPtree
    simpa only [Protocol.Store.toHealing, ← readAt_eq_succ] using hfloor
  have hcompat : Block.compatible P
      (NamedRun.stateBeforeTime S rho (t + 1) w).st.core.F = true := by
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr hFleP
  constructor
  · intro G hG
    rw [activeG2_eq] at hG
    obtain ⟨raw, hframe, hactive⟩ := Option.bind_eq_some_iff.mp hG
    rcases h.1 w hw with hPF | ⟨raw0, hfreeze, hPraw0⟩
    · have hPFnow : Block.Preceq P
          (NamedRun.stateBeforeTime S rho (t + 1) w).st.core.F :=
        Block.preceq_trans hPF
          (incl_strict_F_mono S rho core.toNamedScheduleWellFormed w
            (((domain_le_opening S q).trans hopen).trans htt1le))
      have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        S rho (t + 1) w
      have hFroot : Block.Preceq
          (NamedRun.stateBeforeTime S rho (t + 1) w).st.core.F
          (Protocol.get_fg_root
            (NamedRun.stateBeforeTime S rho (t + 1) w).st.core.toHealing.toFG) :=
        Proofs.Records.preceq_get_fg_root_of_F
          (st := (NamedRun.stateBeforeTime S rho (t + 1) w).st.core.toHealing.toFG)
          (by simpa only [Protocol.Store.toHealing] using hFJ)
      have hGmem := NamedProposalParent.activePrefix_mem
        (Protocol.get_filtered_block_tree
          (NamedRun.readAt S rho t w).st.core.toHealing.toFG) raw G hactive
      have hrootG := Proofs.Records.preceq_get_fg_root_of_mem_filtered hGmem
      exact Block.preceq_trans hPFnow (Block.preceq_trans (by
        simpa only [← readAt_eq_succ] using hFroot) hrootG)
    · have hcomplete := FrameCompleted.frame_g2_completed_in_round
        S rho core w hw q hq (t + 1) hg2lt hsucc hg2hor
      have hfreeze' : DecoupledConsensusModel.Protocol.freezeRoot S.E
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc q .g2) w).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g2) w).st.core.F
          S.hc.η_SG q (early S.E S.hc q .g2) (late S.E S.hc q .g2) = some raw0 := by
        simpa only [postOutageFrozenG2At, postOutageReadAt,
          Proofs.HealingSurface.relativeG2Read, Internal.PhaseGrades.readAt] using hfreeze
      rw [hfreeze'] at hcomplete
      have hframe' : (readFrameAt S (NamedRun.readAt S rho t w)).g2 =
          some (some (DecoupledConsensusModel.Protocol.clipGrade raw0
            (NamedRun.stateBeforeTime S rho (t + 1) w).st.core.F)) := by
        simpa only [readFrameAt, readRound_readAt S rho core.toNamedScheduleWellFormed
          w hw t ht0 hhor, clockRoundAt_eq S t q ht0 hopen hnext,
          ← readAt_eq_succ] using hcomplete
      rw [hframe'] at hframe
      have hraw : DecoupledConsensusModel.Protocol.clipGrade raw0
          (NamedRun.stateBeforeTime S rho (t + 1) w).st.core.F = raw :=
        Option.some.inj hframe
      subst raw
      have hPclip := (q10_retained_prefix raw0
        (NamedRun.stateBeforeTime S rho (t + 1) w).st.core.F P hcompat).mpr hPraw0
      obtain ⟨A, hA, hPA⟩ := activePrefix_covers hPtree (by
        simpa only [← readAt_eq_succ] using hPclip)
      have hactive' : DecoupledConsensusModel.Protocol.activePrefix
          (Protocol.get_filtered_block_tree
            (NamedRun.readAt S rho t w).st.core.toHealing.toFG)
          (DecoupledConsensusModel.Protocol.clipGrade raw0
            (NamedRun.readAt S rho t w).st.core.F) = some G := by
        simpa only [readAt_eq_succ] using hactive
      rw [hA] at hactive'
      exact Option.some.inj hactive' ▸ hPA
  · rcases h.2 w hw with hPF | ⟨raw0, hfreeze, hPraw0⟩
    · have hPFnow : Block.Preceq P
          (NamedRun.stateBeforeTime S rho (t + 1) w).st.core.F :=
        Block.preceq_trans hPF
          (incl_strict_F_mono S rho core.toNamedScheduleWellFormed w
            (by rw [domain_g1_eq_opening]; exact hopen.trans htt1le))
      have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        S rho (t + 1) w
      apply preceq_sgRoot_of_fg_root
      exact Block.preceq_trans (by simpa only [← readAt_eq_succ] using hPFnow)
        (Proofs.Records.preceq_get_fg_root_of_F
          (st := (NamedRun.readAt S rho t w).st.core.toHealing.toFG)
          (by simpa only [Protocol.Store.toHealing, ← readAt_eq_succ] using hFJ))
    · have hcomplete := FrameCompleted.frame_phase_completed_in_round
        S rho core w hw q hq .g1 (t + 1) hg1lt hsucc hg1hor
      have hfreeze' : DecoupledConsensusModel.Protocol.freezeRoot S.E
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc q .g1) w).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g1) w).st.core.F
          S.hc.η_SG q (early S.E S.hc q .g1) (late S.E S.hc q .g1) = some raw0 := by
        simpa only [postOutageFrozenG1At] using hfreeze
      rw [hfreeze'] at hcomplete
      have hframe' : (readFrameAt S (NamedRun.readAt S rho t w)).g1 =
          some (some (DecoupledConsensusModel.Protocol.clipGrade raw0
            (NamedRun.stateBeforeTime S rho (t + 1) w).st.core.F)) := by
        simpa only [readFrameAt, readRound_readAt S rho core.toNamedScheduleWellFormed
          w hw t ht0 hhor, clockRoundAt_eq S t q ht0 hopen hnext,
          ← readAt_eq_succ] using hcomplete
      have hPclip := (q10_retained_prefix raw0
        (NamedRun.stateBeforeTime S rho (t + 1) w).st.core.F P hcompat).mpr hPraw0
      exact preceq_sgRoot_of_g1 S (NamedRun.readAt S rho t w) hframe' hPtree
        (by simpa only [← readAt_eq_succ] using hPclip)

private theorem support_cutoff_lt_next_domain
    (S : Setup V) (q : Round) (u : Time) (hu0 : 0 ≤ u)
    (hcut : u = Protocol.support_cutoff S.E (S.E.slotOf u))
    (hnext : u < opening S.E S.hc (q + 1)) :
    u < domain S.E S.hc (q + 1) .g2 := by
  have hslot : S.E.slotOf u < S.hc.opening_slot (q + 1) := by
    by_contra hnot
    have hle : S.hc.opening_slot (q + 1) ≤ S.E.slotOf u := Nat.le_of_not_gt hnot
    have htime := Protocol.proposal_time_mono S.E hle
    exact (not_le_of_gt hnext)
      (htime.trans (Protocol.proposal_time_slotOf_le S.E hu0))
  have hsucc : S.E.slotOf u + 1 ≤ S.hc.opening_slot (q + 1) :=
    Nat.succ_le_of_lt hslot
  have hcast : (((S.E.slotOf u + 1 : Nat) : Time)) ≤
      ((S.hc.opening_slot (q + 1) : Nat) : Time) := by
    exact_mod_cast hsucc
  have hcoef : (0 : Time) ≤ 4 * S.E.Δ := by
    nlinarith [S.E.Δ_pos]
  have hmul := Int.mul_le_mul_of_nonneg_left hcast hcoef
  rw [hcut]
  unfold Protocol.support_cutoff domain opening Protocol.proposal_time Env.t slotStart
  simp only [Phase.domainOffset]
  push_cast at hmul ⊢
  nlinarith [S.E.Δ_pos]

theorem confirmationDutyRoot_covers
    (S : Setup V) (rho : NamedRun V) (P : Block V) (q : Round)
    (core : NamedAdmissibleCore S rho) (w : V) (hw : w ∈ rho.honest)
    (hq : 0 < q) (u : Time) (hround : S.hc.round_of (S.E.slotOf u) = q)
    (ht : domain S.E S.hc q .g2 < u) (hta : u ≤ opening S.E S.hc (q + 1))
    (hhor : domain S.E S.hc q .g2 ≤ rho.horizon)
    (hroot : Block.Preceq P
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g2) w).st.core.F ∨
      ∃ R, postOutageFrozenG2At S rho w q = some R ∧ Block.Preceq P R)
    (hK6 : Block.Preceq P
        (Protocol.get_fg_root
          (NamedRun.stateBeforeTime S rho u w).st.core.toHealing.toFG) ∨
      P ∈ Protocol.get_filtered_block_tree
        (NamedRun.stateBeforeTime S rho u w).st.core.toHealing.toFG)
    {G : Block V}
    (hG : dutyStableRoot S (NamedActionReads.confirmationReadAt S rho w u) = some G) :
    Block.Preceq P G := by
  let n := NamedActionReads.confirmationReadAt S rho w u
  rcases hK6 with hfg | hPtree
  · have hfg' : Block.Preceq P (Protocol.get_fg_root n.st.core.toHealing.toFG) := by
      simpa only [n, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom] using hfg
    exact Block.preceq_trans hfg' (fgRoot_preceq_dutyStableRoot S n hG)
  rcases hroot with hPF | ⟨raw, hfreeze, hPraw⟩
  · have hPFnow : Block.Preceq P
        (NamedRun.stateBeforeTime S rho u w).st.core.F :=
      Block.preceq_trans hPF
        (incl_strict_F_mono S rho core.toNamedScheduleWellFormed w ht.le)
    have hFJ : Block.preceq n.st.core.F n.st.core.J = true := by
      change Block.preceq
        (NamedRun.stateBeforeTime S rho u w).st.core.F
        (NamedRun.stateBeforeTime S rho u w).st.core.J = true
      exact Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho u w
    have hFroot : Block.Preceq n.st.core.F
        (Protocol.get_fg_root n.st.core.toHealing.toFG) :=
      Proofs.Records.preceq_get_fg_root_of_F (st := n.st.core.toHealing.toFG)
        (by simpa only [Protocol.Store.toHealing] using hFJ)
    have hPFn : Block.Preceq P n.st.core.F := by
      simpa only [n, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom] using hPFnow
    exact Block.preceq_trans hPFn
      (Block.preceq_trans hFroot (fgRoot_preceq_dutyStableRoot S n hG))
  · have hFleP : Block.Preceq
        (NamedRun.stateBeforeTime S rho u w).st.core.F P := by
      have hf := q10_filtered_F hPtree
      simpa only [Protocol.Store.toHealing] using hf
    have hcompat : Block.compatible P
        (NamedRun.stateBeforeTime S rho u w).st.core.F = true := by
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr hFleP
    have hclip : Block.Preceq P
        (DecoupledConsensusModel.Protocol.clipGrade raw
          (NamedRun.stateBeforeTime S rho u w).st.core.F) :=
      (q10_retained_prefix raw
        (NamedRun.stateBeforeTime S rho u w).st.core.F P hcompat).mpr hPraw
    have hfreeze' : DecoupledConsensusModel.Protocol.freezeRoot S.E
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc q .g2) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc q .g2) w).st.core.F S.hc.η_SG q
        (early S.E S.hc q .g2) (late S.E S.hc q .g2) = some raw := by
      simpa only [postOutageFrozenG2At, postOutageReadAt,
        Proofs.HealingSurface.relativeG2Read, Internal.PhaseGrades.readAt] using hfreeze
    have hbase := FrameCompleted.frame_g2_completed_in_round
      S rho core w hw q hq u ht hta hhor
    have hframe := frame_phase_prepared_eq S rho w q .g2 u hround _ hbase
    rw [hfreeze'] at hframe
    have hnround : S.hc.round_of n.st.core.s = q := by
      simpa only [n, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom] using hround
    have hframe' : (DecoupledConsensusModel.Protocol.readFrame n.cache
        n.st.core.toHealing q).g2 =
        some (some (DecoupledConsensusModel.Protocol.clipGrade raw
          (NamedRun.stateBeforeTime S rho u w).st.core.F)) := by
      simpa only [n, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom] using hframe
    have hPtreeN : P ∈ Protocol.get_filtered_block_tree
        n.st.core.toHealing.toFG := by
      dsimp only [n]
      change P ∈ Protocol.get_filtered_block_tree
        (NamedRun.stateBeforeTime S rho u w).st.core.toHealing.toFG
      exact hPtree
    have hg2read : (readFrameAt S n).g2 =
        some (some (DecoupledConsensusModel.Protocol.clipGrade raw
          (NamedRun.stateBeforeTime S rho u w).st.core.F)) := by
      change (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing
        (S.hc.round_of n.st.core.s)).g2 = _
      rw [hnround]
      exact hframe'
    obtain ⟨A, hA, hPA⟩ := activeG2_covers S n hg2read hPtreeN (by
        simpa only [n, NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom] using hclip)
    rw [dutyStableRoot_eq_activeG2, hA] at hG
    exact Option.some.inj hG ▸ hPA


theorem prepared_outputs_eq_strict
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (w : V) (hw : w ∈ rho.honest) (q : Round) (hq : 0 < q) (u : Time)
    (hu0 : 0 ≤ u) (hround : clockRoundAt S u = q)
    (hcut : u = Protocol.support_cutoff S.E (S.E.slotOf u))
    (hhor : u ≤ rho.horizon) :
    activeG2 S (NamedActionReads.confirmationReadAt S rho w u) =
        activeG2 S (NamedRun.readAt S rho (u - 1) w) ∧
      sgRoot S (NamedActionReads.confirmationReadAt S rho w u) =
        sgRoot S (NamedRun.readAt S rho (u - 1) w) := by
  have hopen : opening S.E S.hc q < u := by
    rw [← hround]
    exact opening_lt_support_cutoff S u hu0 hcut
  have hopenPred : opening S.E S.hc q ≤ u - 1 := Int.le_sub_one_iff.mpr hopen
  have hnext : u < opening S.E S.hc (q + 1) := by
    rw [← hround]
    exact clockRound_lt_opening_succ S u
  have hpredNext : u - 1 < opening S.E S.hc (q + 1) :=
    (Int.sub_le_self u (by norm_num)).trans_lt hnext
  have hpred0 : (0 : Time) ≤ u - 1 :=
    (base_opening_nonneg S q).trans hopenPred
  have hpredHor : u - 1 ≤ rho.horizon :=
    (Int.sub_le_self u (by norm_num)).trans hhor
  have hreadRound : readRound S (NamedRun.readAt S rho (u - 1) w) = q := by
    rw [readRound_readAt S rho core.toNamedScheduleWellFormed w hw
      (u - 1) hpred0 hpredHor]
    exact clockRoundAt_eq S (u - 1) q hpred0 hopenPred hpredNext
  have hstrict : NamedRun.readAt S rho (u - 1) w =
      NamedRun.stateBeforeTime S rho u w := by
    rw [readAt_eq_succ]
    congr 2
    ring
  have hdomG2 : domain S.E S.hc q .g2 < u :=
    lt_of_le_of_lt (domain_le_opening S q) hopen
  have hdomG1 : domain S.E S.hc q .g1 < u := by
    rw [domain_g1_eq_opening]
    exact hopen
  have hdomG2Hor : domain S.E S.hc q .g2 ≤ rho.horizon :=
    hdomG2.le.trans hhor
  have hdomG1Hor : domain S.E S.hc q .g1 ≤ rho.horizon :=
    hdomG1.le.trans hhor
  have hg2 := FrameCompleted.frame_phase_completed_in_round S rho core w hw q hq .g2 u
    hdomG2 hnext.le hdomG2Hor
  have hg1 := FrameCompleted.frame_phase_completed_in_round S rho core w hw q hq .g1 u
    hdomG1 hnext.le hdomG1Hor
  have hg2p := frame_phase_prepared_eq S rho w q .g2 u hround _ hg2
  have hg1p := frame_phase_prepared_eq S rho w q .g1 u hround _ hg1
  have hroundPrepared : readRound S
      (NamedActionReads.confirmationReadAt S rho w u) = q := by
    change S.hc.round_of (S.E.slotOf u) = q
    exact hround
  have htreePrepared : Protocol.get_filtered_block_tree
      (NamedActionReads.confirmationReadAt S rho w u).st.core.toHealing.toFG =
      Protocol.get_filtered_block_tree
        (NamedRun.readAt S rho (u - 1) w).st.core.toHealing.toFG := by
    change Protocol.get_filtered_block_tree
        (NamedRun.stateBeforeTime S rho u w).st.core.toHealing.toFG = _
    rw [hstrict]
  have hrootPrepared : Protocol.get_fg_root
      (NamedActionReads.confirmationReadAt S rho w u).st.core.toHealing.toFG =
      Protocol.get_fg_root
        (NamedRun.readAt S rho (u - 1) w).st.core.toHealing.toFG := by
    change Protocol.get_fg_root
        (NamedRun.stateBeforeTime S rho u w).st.core.toHealing.toFG = _
    rw [hstrict]
  constructor
  · rw [activeG2_eq, activeG2_eq]
    rw [show (readFrameAt S (NamedActionReads.confirmationReadAt S rho w u)).g2 =
        (readFrameAt S (NamedRun.readAt S rho (u - 1) w)).g2 by
      rw [readFrameAt, readFrameAt, hroundPrepared, hreadRound, hstrict]
      simpa only [Internal.NamedOutageEntry.confirmationReadAt] using hg2p.trans hg2.symm]
    rw [htreePrepared]
  · rw [sgRoot_eq, sgRoot_eq, hroundPrepared, hreadRound]
    rw [show (readFrameAt S (NamedActionReads.confirmationReadAt S rho w u)).g1 =
        (readFrameAt S (NamedRun.readAt S rho (u - 1) w)).g1 by
      rw [readFrameAt, readFrameAt, hroundPrepared, hreadRound, hstrict]
      simpa only [Internal.NamedOutageEntry.confirmationReadAt] using hg1p.trans hg1.symm]
    unfold DecoupledConsensusModel.Protocol.anchor
    rw [htreePrepared, hrootPrepared]


private theorem clockRoundAt_mono (S : Setup V) {a b : Time} (h : a ≤ b) :
    clockRoundAt S a ≤ clockRoundAt S b := by
  have hpos : (0 : Time) < 4 * S.E.Δ := Int.mul_pos (by decide) S.E.Δ_pos
  have hslot : S.E.slotOf a ≤ S.E.slotOf b := by
    simp only [Env.slotOf, slotOfTime]
    rw [Int.fdiv_eq_ediv_of_nonneg _ hpos.le,
      Int.fdiv_eq_ediv_of_nonneg _ hpos.le]
    exact Int.toNat_le_toNat (Int.ediv_le_ediv hpos h)
  exact Nat.div_le_div_right hslot

private theorem healthySeed_round_le_action (S : Setup V) (r : Round) :
    (r : Time) ≤ S.a r := by
  have hR : 0 < S.hc.R := lt_of_lt_of_le (by decide) S.hc.R_ge_two
  have hRcast : (0 : Time) < (S.hc.R : Time) := by
    exact_mod_cast hR
  have hscale : (1 : Time) ≤ 4 * S.E.Δ * (S.hc.R : Time) := by
    have hpos := Int.mul_pos
      (Int.mul_pos (show (0 : Time) < 4 by norm_num) S.E.Δ_pos) hRcast
    exact Int.add_one_le_iff.mpr hpos
  have hscaled : (r : Time) ≤
      (4 * S.E.Δ * (S.hc.R : Time)) * (r : Time) := by
    simpa only [one_mul] using
      Int.mul_le_mul_of_nonneg_right hscale (Int.natCast_nonneg r)
  have hpad : (0 : Time) ≤ 6 * S.E.Δ := by
    exact Int.mul_nonneg (by norm_num) S.E.Δ_pos.le
  calc
    (r : Time) ≤ (4 * S.E.Δ * (S.hc.R : Time)) * (r : Time) := hscaled
    _ ≤ (4 * S.E.Δ * (S.hc.R : Time)) * (r : Time) + 6 * S.E.Δ :=
      le_add_of_nonneg_right hpad
    _ = S.a r := by
      unfold Setup.a Protocol.HealConfig.a Protocol.HealConfig.opening_slot slotStart
      push_cast
      ring




/-- Select the first positive round whose action is in the healthy regime. -/
theorem firstHealthyAction_exists
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s : Round)
    (hexec : OutageExecution S rho b0 b1)
    (hmargin : FormationMargin S s b0) :
    ∃ r0 : Round, 0 < r0 ∧ max S.E.t_GST b1 ≤ S.a r0 ∧
      (∀ q : Round, 0 < q → max S.E.t_GST b1 ≤ S.a q → r0 ≤ q) ∧
      S.a (r0 - 1) < max S.E.t_GST b1 := by
  have hex : ∃ r : Round, max S.E.t_GST b1 ≤ S.a r := by
    obtain ⟨r, hr⟩ := exists_nat_gt (max S.E.t_GST b1)
    exact ⟨r, hr.le.trans (healthySeed_round_le_action S r)⟩
  let r0 := Nat.find hex
  have hbound : max S.E.t_GST b1 ≤ S.a r0 := Nat.find_spec hex
  have ha0 : S.a 0 < max S.E.t_GST b1 := by
    calc
      S.a 0 ≤ S.a (s + 1) := Assembly.a_mono S (Nat.zero_le _)
      _ < S.a (s + 1) + S.E.Δ := lt_add_of_pos_right _ S.E.Δ_pos
      _ ≤ b0 := hmargin
      _ ≤ b1 := hexec.interval.2.1
      _ ≤ max S.E.t_GST b1 := le_max_right _ _
  have hpos : 0 < r0 := by
    by_contra hnot
    have hz : r0 = 0 := by omega
    rw [hz] at hbound
    exact (not_le_of_gt ha0) hbound
  have hminimal : ∀ q : Round, 0 < q →
      max S.E.t_GST b1 ≤ S.a q → r0 ≤ q := by
    intro q _ hq
    exact Nat.find_min' hex hq
  have hpred : r0 - 1 < r0 := by omega
  have hcut : S.a (r0 - 1) < max S.E.t_GST b1 :=
    lt_of_not_ge (Nat.find_min hex hpred)
  exact ⟨r0, hpos, hbound, hminimal, hcut⟩


/-- A seed action has one full delivery delay before the next G2 early cut. -/
theorem healthyAction_add_delta_le_next_earlyG2
    (S : Setup V) (r : Round) :
    S.a r + S.E.Δ ≤ early S.E S.hc (r + 1) .g2 :=
  source_deadline_le_next_early S r S.hc.R_ge_three


/-- Votes cast before the outage use the healthy-prefix deadline. -/
theorem preBoundary_emitted_sg_at_next_g2
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1) {a : NamedAttestation V}
    (ha : a.val_index ∈ rho.honest)
    (hem : NamedRun.emits S rho a.val_index (.attest a) (S.a a.round))
    (hbefore : S.a a.round < b0) :
    ∀ reader ∈ rho.honest,
      let r := a.round + 1
      let n := NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) reader
      a ∈ n.st.sg_rows a.round ∧
      occurrenceBefore (n.st.core.timestamp_sg_vote (Protocol.sgVote a.erase))
        (early S.E S.hc r .g2) = true ∧
      Protocol.sgVote a.erase ∈ rawInputs n.st.core.toHealing.gradeView
        S.hc.η_SG r (early S.E S.hc r .g2) a.val_index := by
  exact SGArrivalDeadline.healthy_emitted_sg_at_next_g2_of_deadline
    S rho b0 b1 hexec ha hem
      (a_add_delta_le_of_lt_public S b0 hexec.boundaryPublic a.round hbefore)

def TransitionSGClauses
    (S : Setup V) (rho : NamedRun V) (b0 : Time)
    (Pn : NamedBlock V) (r0 : Round) : Prop :=
  ∀ r : Round, DomainIncluded S rho b0 r → r ≤ r0 →
    ∀ w ∈ rho.honest,
      let n := NamedRun.readAt S rho (domain S.E S.hc r .g1) w
      Block.Preceq Pn.erase n.st.core.F ∨
        ∃ raw : Block V,
          (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g2 =
            some (some raw) ∧ Block.Preceq Pn.erase raw

private theorem transition_sg_at_clockRound
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r0 : Round)
    (Pn : NamedBlock V) (hmargin : FormationMargin S s b0)
    (hsgs : TransitionSGClauses S rho b0 Pn r0)
    (hframes : PreBoundaryFrames S rho b0 s Pn.erase)
    (w : V) (hw : w ∈ rho.honest) (t : Time) (hb0 : b0 ≤ t)
    (hround : clockRoundAt S t ≤ r0) (hhor : t ≤ rho.horizon) :
    Block.Preceq Pn.erase
        (NamedRun.readAt S rho
          (domain S.E S.hc (clockRoundAt S t) .g1) w).st.core.F ∨
      ∃ raw : Block V,
        (DecoupledConsensusModel.Protocol.readFrame
            (NamedRun.readAt S rho
              (domain S.E S.hc (clockRoundAt S t) .g1) w).cache
            (NamedRun.readAt S rho
              (domain S.E S.hc (clockRoundAt S t) .g1) w).st.core.toHealing
            (clockRoundAt S t)).g2 = some (some raw) ∧
          Block.Preceq Pn.erase raw := by
  have hqpos : 0 < clockRoundAt S t :=
    Nat.lt_of_lt_of_le (Nat.succ_pos s)
      (succ_le_clockRound S s b0 t hmargin hb0)
  by_cases haction : b0 ≤ S.a (clockRoundAt S t)
  · have hsix0 : (0 : Time) ≤ 6 * S.E.Δ := by
      nlinarith [S.E.Δ_pos]
    have ht0 : (0 : Time) ≤ t :=
      hsix0.trans ((six_delta_lt_b0 S s b0 hmargin).le.trans hb0)
    have hinc : DomainIncluded S rho b0 (clockRoundAt S t) := by
      refine ⟨hqpos, haction, ?_⟩
      rw [domain_g1_eq_opening]
      exact (opening_le_clockRound S t ht0).trans hhor
    exact hsgs (clockRoundAt S t) hinc hround w hw
  · exact hframes w hw (clockRoundAt S t)
      (succ_le_clockRound S s b0 t hmargin hb0) (not_le.mp haction)

private theorem transition_read_floors
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r0 : Round)
    (Pn : NamedBlock V) (core : NamedAdmissibleCore S rho)
    (hmargin : FormationMargin S s b0)
    (hsgs : TransitionSGClauses S rho b0 Pn r0)
    (hframes : PreBoundaryFrames S rho b0 s Pn.erase)
    (hK6all : ∀ t, b0 ≤ t → t ≤ rho.horizon → ∀ u ∈ rho.honest,
      Block.Preceq Pn.erase
          (Protocol.get_fg_root
            (NamedRun.readAt S rho t u).st.core.toHealing.toFG) ∨
        Pn.erase ∈ Internal.PhaseGrades.filteredTree (NamedRun.readAt S rho t u))
    (w : V) (hw : w ∈ rho.honest) (t : Time) (hb0 : b0 ≤ t)
    (hround : clockRoundAt S t ≤ r0) (hhor : t ≤ rho.horizon) :
    (∀ G, activeG2 S (NamedRun.readAt S rho t w) = some G →
      Block.Preceq Pn.erase G) ∧
      Block.Preceq Pn.erase (sgRoot S (NamedRun.readAt S rho t w)) := by
  have hsix0 : (0 : Time) ≤ 6 * S.E.Δ := by
    nlinarith [S.E.Δ_pos]
  have ht0 : (0 : Time) ≤ t :=
    hsix0.trans ((six_delta_lt_b0 S s b0 hmargin).le.trans hb0)
  have hqpos : 0 < clockRoundAt S t :=
    Nat.lt_of_lt_of_le (Nat.succ_pos s)
      (succ_le_clockRound S s b0 t hmargin hb0)
  have hsg := transition_sg_at_clockRound S rho b0 b1 s r0 Pn
    hmargin hsgs hframes w hw t hb0 hround hhor
  have hK6 := hK6all t hb0 hhor w hw
  have hcompat : Block.compatible Pn.erase
      (NamedRun.readAt S rho t w).st.core.F = true := by
    rcases hK6 with hroot | htree
    · have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_readAt S rho t w
      have hFroot := Proofs.Records.preceq_get_fg_root_of_F
        (st := (NamedRun.readAt S rho t w).st.core.toHealing.toFG)
        (by simpa only [Protocol.Store.toHealing] using hFJ)
      exact Block.compatible_of_preceq_common hroot hFroot
    · simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr (q10_filtered_F htree)
  have hmain := read_conjuncts_of_sg S rho core w hw Pn.erase
    (clockRoundAt S t) hqpos t ht0 (opening_le_clockRound S t ht0)
    (Int.add_one_le_iff.mpr (clockRound_lt_opening_succ S t)) hhor hsg
    hK6 hcompat
  refine ⟨?_, hmain.2⟩
  intro G hG
  rcases hmain.1 with hroot | ⟨A, hA, hPA⟩
  · exact Block.preceq_trans hroot
      (Proofs.Records.preceq_get_fg_root_of_mem_filtered
        (by
          rw [activeG2_eq] at hG
          obtain ⟨raw, _, hactive⟩ := Option.bind_eq_some_iff.mp hG
          exact NamedProposalParent.activePrefix_mem _ raw G hactive))
  · exact Option.some.inj (hA.symm.trans hG) ▸ hPA

private theorem transition_prepared_floors
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r0 : Round)
    (Pn : NamedBlock V) (core : NamedAdmissibleCore S rho)
    (hmargin : FormationMargin S s b0)
    (hsgs : TransitionSGClauses S rho b0 Pn r0)
    (hframes : PreBoundaryFrames S rho b0 s Pn.erase)
    (hK6all : ∀ t, b0 ≤ t → t ≤ rho.horizon → ∀ u ∈ rho.honest,
      Block.Preceq Pn.erase
          (Protocol.get_fg_root
            (NamedRun.readAt S rho t u).st.core.toHealing.toFG) ∨
        Pn.erase ∈ Internal.PhaseGrades.filteredTree (NamedRun.readAt S rho t u))
    (w : V) (hw : w ∈ rho.honest) (u : Time) (hb0 : b0 < u)
    (hround : clockRoundAt S u ≤ r0) (hhor : u ≤ rho.horizon)
    (hcut : u = Protocol.support_cutoff S.E (S.E.slotOf u)) :
    Block.Preceq Pn.erase (sgRoot S (confirmationReadAt S rho w u)) ∧
      ∀ G, activeG2 S (confirmationReadAt S rho w u) = some G →
        Block.Preceq Pn.erase G := by
  have hsix0 : (0 : Time) ≤ 6 * S.E.Δ := by
    nlinarith [S.E.Δ_pos]
  have hu0 : (0 : Time) ≤ u :=
    hsix0.trans ((six_delta_lt_b0 S s b0 hmargin).le.trans hb0.le)
  have hqpos : 0 < clockRoundAt S u :=
    Nat.lt_of_lt_of_le (Nat.succ_pos s)
      (succ_le_clockRound S s b0 u hmargin hb0.le)
  have hsg := transition_sg_at_clockRound S rho b0 b1 s r0 Pn
    hmargin hsgs hframes w hw u hb0.le hround hhor
  have hb0pred : b0 ≤ u - 1 := Int.le_sub_one_iff.mpr hb0
  have hpredHor : u - 1 ≤ rho.horizon :=
    (Int.sub_le_self u (by norm_num)).trans hhor
  have htree := hK6all (u - 1) hb0pred hpredHor w hw
  have hpredSucc : u - 1 + 1 = u := by ring
  rw [readAt_eq_succ, hpredSucc] at htree
  have hcompat : Block.compatible Pn.erase
      (NamedRun.stateBeforeTime S rho u w).st.core.F = true := by
    rcases htree with hroot | hPtree
    · have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        S rho u w
      have hFroot := Proofs.Records.preceq_get_fg_root_of_F
        (st := (NamedRun.stateBeforeTime S rho u w).st.core.toHealing.toFG)
        (by simpa only [Protocol.Store.toHealing] using hFJ)
      exact Block.compatible_of_preceq_common hroot hFroot
    · simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr (q10_filtered_F hPtree)
  exact candidate_at_cutoff_of_sg S rho core w hw Pn.erase
    (clockRoundAt S u) hqpos u rfl (opening_lt_support_cutoff S u hu0 hcut)
    (clockRound_lt_opening_succ S u).le
    ((opening_le_clockRound S u hu0).trans hhor) hsg htree hcompat

private theorem transition_stable
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r0 : Round)
    (Pn : NamedBlock V) (core : NamedAdmissibleCore S rho)
    (hb0b1 : b0 ≤ b1) (hmargin : FormationMargin S s b0)
    (hsgs : TransitionSGClauses S rho b0 Pn r0)
    (hframes : PreBoundaryFrames S rho b0 s Pn.erase)
    (hout : StableUserOutputs S rho b0 b1 Pn.erase)
    (hK6all : ∀ t, b0 ≤ t → t ≤ rho.horizon → ∀ u ∈ rho.honest,
      Block.Preceq Pn.erase
          (Protocol.get_fg_root
            (NamedRun.readAt S rho t u).st.core.toHealing.toFG) ∨
        Pn.erase ∈ Internal.PhaseGrades.filteredTree (NamedRun.readAt S rho t u))
    (w : V) (hw : w ∈ rho.honest) (t : Time)
    (hcap : b1 + S.E.Δ < t) (hround : clockRoundAt S t ≤ r0)
    (hhor : t ≤ rho.horizon) :
    Block.Preceq Pn.erase
      (Protocol.get_stable (NamedRun.readAt S rho t w).st.core) := by
  let start := b1 + S.E.Δ + 1
  let stop := t + 1
  let i := (rho.events.filter (fun e => decide (e.time < start))).length
  let j := (rho.events.filter (fun e => decide (e.time < stop))).length
  have hstartStop : start ≤ stop := by
    dsimp only [start, stop]
    exact Int.add_le_add_right hcap.le 1
  have hi : NamedRun.stateBeforeTime S rho start w =
      NamedRun.stateBefore S rho i w :=
    congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S
      core.toNamedScheduleWellFormed start) w
  have hj : NamedRun.stateBeforeTime S rho stop w =
      NamedRun.stateBefore S rho j w :=
    congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S
      core.toNamedScheduleWellFormed stop) w
  have hij : i ≤ j := by
    dsimp only [i, j]
    exact strict_lengths_mono rho hstartStop
  have hb0cap : b0 ≤ b1 + S.E.Δ :=
    hb0b1.trans (Int.le_add_of_nonneg_right S.E.Δ_pos.le)
  have hcapHor : b1 + S.E.Δ ≤ rho.horizon := hcap.le.trans hhor
  have hstartStable : Block.Preceq Pn.erase
      (Protocol.get_stable
        (NamedRun.stateBeforeTime S rho start w).st.core) := by
    have hh := (hout w hw (b1 + S.E.Δ) hb0cap le_rfl hcapHor).1
    dsimp only [start]
    simpa only [← readAt_eq_succ] using hh
  have hhold : Block.Preceq Pn.erase
      (NamedRun.stateBefore S rho i w).st.core.F ∨
      Block.Preceq Pn.erase
        (NamedRun.stateBefore S rho i w).st.core.latest_stable := by
    rw [← hi]
    unfold Protocol.get_stable at hstartStable
    split at hstartStable
    · exact Or.inr hstartStable
    · exact Or.inl hstartStable
  have hcases := stateBefore_stable_covered_of_comparable S rho w i j hij hhold
    (fun k u hik hkj he hpos hcut G hG _ => by
      have huStart : start ≤ u := Proofs.Optimistic.le_time_of_index_ge S
        core.toNamedScheduleWellFormed (t := start) (j := k) hik he
      have huStop : u < stop := by
        have hins := Proofs.Optimistic.filter_true_of_index_lt S
          core.toNamedScheduleWellFormed
          (fun e => decide (e.time < stop)) (Proofs.Optimistic.downward_lt stop) hkj he
        simpa only [decide_eq_true_eq, NamedEvent.time] using hins
      have hut : u ≤ t := by
        dsimp only [stop] at huStop
        exact Int.lt_add_one_iff.mp huStop
      have hb0u : b0 < u := by
        dsimp only [start] at huStart
        exact lt_of_le_of_lt hb0cap
          (lt_of_lt_of_le (Int.lt_add_one_iff.mpr le_rfl) huStart)
      have huHor : u ≤ rho.horizon := hut.trans hhor
      have hqu : clockRoundAt S u ≤ r0 :=
        (clockRoundAt_mono S hut).trans hround
      have hfloors := transition_prepared_floors S rho b0 b1 s r0 Pn
        core hmargin hsgs hframes hK6all w hw u hb0u hqu
        huHor hcut
      have hbefore := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S
        core.toNamedScheduleWellFormed he
      change NamedRun.stateBefore S rho k w =
        NamedRun.stateBeforeTime S rho u w at hbefore
      have hread : NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S rho k w) u =
          NamedActionReads.confirmationReadAt S rho w u := by
        rw [hbefore]
        rfl
      have hG' : dutyStableRoot S
          (NamedActionReads.confirmationReadAt S rho w u) = some G := by
        rw [← hread]
        exact hG
      rw [dutyStableRoot_eq_activeG2] at hG'
      cases hactive : activeG2 S
          (NamedActionReads.confirmationReadAt S rho w u) with
      | none =>
          rw [hactive] at hG'
          have hb0pred : b0 ≤ u - 1 := Int.le_sub_one_iff.mpr hb0u
          have hpredHor : u - 1 ≤ rho.horizon :=
            (Int.sub_le_self u (by norm_num)).trans huHor
          have htree := hK6all (u - 1) hb0pred hpredHor w hw
          have hpredSucc : u - 1 + 1 = u := by ring
          rw [readAt_eq_succ, hpredSucc] at htree
          rcases htree with hroot | htree
          · left
            rw [← Option.some.inj hG']
            simpa only [NamedActionReads.confirmationReadAt,
              NamedActionReads.confirmationReadFrom] using hroot
          · right
            rw [← Option.some.inj hG']
            exact Proofs.Records.preceq_get_fg_root_of_mem_filtered htree
      | some A =>
          rw [hactive] at hG'
          left
          exact Option.some.inj hG' ▸ hfloors.2 A hactive)
  have htree := hK6all t
    (hb0cap.trans hcap.le) hhor w hw
  have hcompat : Block.compatible Pn.erase
      (NamedRun.stateBeforeTime S rho stop w).st.core.F = true := by
    rcases htree with hroot | htree
    · have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        S rho stop w
      have hFroot := Proofs.Records.preceq_get_fg_root_of_F
        (st := (NamedRun.stateBeforeTime S rho stop w).st.core.toHealing.toFG)
        (by simpa only [Protocol.Store.toHealing] using hFJ)
      have hrootStop : Block.Preceq Pn.erase
          (Protocol.get_fg_root
            (NamedRun.stateBeforeTime S rho stop w).st.core.toHealing.toFG) := by
        dsimp only [stop]
        simpa only [← readAt_eq_succ] using hroot
      exact Block.compatible_of_preceq_common hrootStop hFroot
    · have hFleP := q10_filtered_F htree
      dsimp only [stop]
      simpa only [← readAt_eq_succ, Block.compatible, Bool.or_eq_true]
        using (Or.inr hFleP : Block.Preceq Pn.erase
          (NamedRun.readAt S rho t w).st.core.F ∨
            Block.Preceq (NamedRun.readAt S rho t w).st.core.F Pn.erase)
  rw [readAt_eq_succ]
  change Block.Preceq Pn.erase
    (Protocol.get_stable (NamedRun.stateBeforeTime S rho stop w).st.core)
  rw [hj]
  rw [hj] at hcompat
  exact preceq_get_stable_of_cases _ hcases hcompat

theorem stableUserOutputs_transition_of_sg
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r0 : Round)
    (Pn : NamedBlock V) (core : NamedAdmissibleCore S rho)
    (hb0b1 : b0 ≤ b1) (hmargin : FormationMargin S s b0)
    (hsgs : TransitionSGClauses S rho b0 Pn r0)
    (hframes : PreBoundaryFrames S rho b0 s Pn.erase)
    (hout : StableUserOutputs S rho b0 b1 Pn.erase)
    (hK6all : ∀ t, b0 ≤ t → t ≤ rho.horizon → ∀ u ∈ rho.honest,
      Block.Preceq Pn.erase
          (Protocol.get_fg_root
            (NamedRun.readAt S rho t u).st.core.toHealing.toFG) ∨
        Pn.erase ∈ Internal.PhaseGrades.filteredTree (NamedRun.readAt S rho t u)) :
    ∀ w ∈ rho.honest, ∀ t, b1 + S.E.Δ < t → b0 ≤ t →
      clockRoundAt S t ≤ r0 → t ≤ rho.horizon →
      let n := NamedRun.readAt S rho t w
      Block.Preceq Pn.erase (Protocol.get_stable n.st.core) ∧
      (∀ G, activeG2 S n = some G → Block.Preceq Pn.erase G) ∧
      (∀ u, b0 ≤ u → u ≤ t → ∀ B,
        CandidateWritten S rho w u B → Block.Preceq Pn.erase B) := by
  intro w hw t hcap hb0 hround hhor
  have hstable := transition_stable S rho b0 b1 s r0 Pn core
    hb0b1 hmargin hsgs hframes hout hK6all w hw t hcap
    hround hhor
  have hfloors := transition_read_floors S rho b0 b1 s r0 Pn core
    hmargin hsgs hframes hK6all w hw t hb0 hround hhor
  refine ⟨hstable, hfloors.1, ?_⟩
  intro u hb0u hut B hB
  by_cases hucap : u ≤ b1 + S.E.Δ
  · have hcapHor : b1 + S.E.Δ ≤ rho.horizon := hcap.le.trans hhor
    have hb0cap : b0 ≤ b1 + S.E.Δ :=
      hb0b1.trans (Int.le_add_of_nonneg_right S.E.Δ_pos.le)
    exact (hout w hw (b1 + S.E.Δ) hb0cap le_rfl hcapHor).2.2
      u hb0u hucap B hB
  · obtain ⟨i, he, hpos, hcut, hcand⟩ := hB
    have hb0u' : b0 < u :=
      (hb0b1.trans (Int.le_add_of_nonneg_right S.E.Δ_pos.le)).trans_lt
        (lt_of_not_ge hucap)
    have huHor : u ≤ rho.horizon := hut.trans hhor
    have hqu : clockRoundAt S u ≤ r0 :=
      (clockRoundAt_mono S hut).trans hround
    have hprepared := transition_prepared_floors S rho b0 b1 s r0 Pn
      core hmargin hsgs hframes hK6all w hw u hb0u' hqu
      huHor hcut
    have hbefore := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S
      core.toNamedScheduleWellFormed he
    have hbefore' : NamedRun.stateBefore S rho i w =
        NamedRun.stateBeforeTime S rho u w := by
      simpa only using hbefore
    have hread : NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBefore S rho i w) u = confirmationReadAt S rho w u := by
      rw [hbefore']
      rfl
    have hcand' : confirmationCandidate S
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S rho i w) u) (S.E.slotOf u - 1) = some B := by
      simpa only [Internal.NamedOutageEntry.confirmationReadFrom] using hcand
    rw [hread] at hcand'
    exact candidate_covers S _ _ hcand' hprepared.1 hprepared.2






/-- Once the round induction supplies every horizon-local post-outage
certificate, all three public output clauses follow. K6 is used at each exact
read and immediately before each confirmation duty. -/
theorem stableUserOutputsFrom_of_induction
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r0 : Round)
    (P : Block V)
    (core : NamedAdmissibleCore S rho) (hb0b1 : b0 ≤ b1)
    (hmargin : FormationMargin S s b0)
    (hout : StableUserOutputs S rho b0 b1 P)
    (htransition : ∀ w ∈ rho.honest, ∀ t, b1 + S.E.Δ < t → b0 ≤ t →
      clockRoundAt S t ≤ r0 → t ≤ rho.horizon →
      let n := NamedRun.readAt S rho t w
      Block.Preceq P (Protocol.get_stable n.st.core) ∧
      (∀ G, activeG2 S n = some G → Block.Preceq P G) ∧
      (∀ u, b0 ≤ u → u ≤ t → ∀ B,
        CandidateWritten S rho w u B → Block.Preceq P B))
    (hpost : ∀ q, r0 < q → 0 < q → domain S.E S.hc q .g1 ≤ rho.horizon →
      PostOutageAboveTruncated S rho P q)
    (hK6all : ∀ t, b0 ≤ t → t ≤ rho.horizon → ∀ u ∈ rho.honest,
      Block.Preceq P
          (Protocol.get_fg_root
            (NamedRun.readAt S rho t u).st.core.toHealing.toFG) ∨
        P ∈ Internal.PhaseGrades.filteredTree (NamedRun.readAt S rho t u)) :
    StableUserOutputsFrom S rho b0 P := by
  intro w hw t hb0 hhor
  by_cases hcap : t ≤ b1 + S.E.Δ
  · exact hout w hw t hb0 hcap hhor
  let q := clockRoundAt S t
  by_cases hqTransition : q ≤ r0
  · exact htransition w hw t (lt_of_not_ge hcap) hb0 hqTransition hhor
  have hc t' (ht' : b0 ≤ t') (ht'hor : t' ≤ rho.horizon) :
      Block.Preceq P
          (Protocol.get_fg_root
            (NamedRun.readAt S rho t' w).st.core.toHealing.toFG) ∨
        P ∈ Protocol.get_filtered_block_tree
          (NamedRun.readAt S rho t' w).st.core.toHealing.toFG :=
    hK6all t' ht' ht'hor w hw
  have hsix0 : (0 : Time) ≤ 6 * S.E.Δ := by
    nlinarith [S.E.Δ_pos]
  have ht0 : (0 : Time) ≤ t :=
    hsix0.trans ((six_delta_lt_b0 S s b0 hmargin).le.trans hb0)
  have hb0cap : b0 ≤ b1 + S.E.Δ :=
    hb0b1.trans (Int.le_add_of_nonneg_right S.E.Δ_pos.le)
  have hcapHor : b1 + S.E.Δ ≤ rho.horizon :=
    (lt_of_not_ge hcap).le.trans hhor
  have hopen : opening S.E S.hc q ≤ t := opening_le_clockRound S t ht0
  have hnext : t < opening S.E S.hc (q + 1) := clockRound_lt_opening_succ S t
  have hq : 0 < q :=
    Nat.lt_of_lt_of_le (Nat.succ_pos s) (succ_le_clockRound S s b0 t hmargin hb0)
  have hqHor : domain S.E S.hc q .g1 ≤ rho.horizon := by
    rw [domain_g1_eq_opening]
    exact hopen.trans hhor
  have hpostq := hpost q (Nat.lt_of_not_ge hqTransition) hq hqHor
  have hfloors := output_floors_at_read S rho P q core hpostq.1 w hw t ht0 hq
    hopen hnext hhor (hc t hb0 hhor)
  refine ⟨?_, hfloors.1, ?_⟩
  · let start := b1 + S.E.Δ + 1
    let i := (rho.events.filter (fun e => decide (e.time < start))).length
    let j := (rho.events.filter (fun e => decide (e.time < t + 1))).length
    have hcaplt : b1 + S.E.Δ < t := lt_of_not_ge hcap
    have hstartEnd : start ≤ t + 1 := by
      dsimp only [start]
      exact Int.add_le_add_right hcaplt.le 1
    have hi : NamedRun.stateBeforeTime S rho start w =
        NamedRun.stateBefore S rho i w :=
      congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S core.toNamedScheduleWellFormed start) w
    have hj : NamedRun.stateBeforeTime S rho (t + 1) w =
        NamedRun.stateBefore S rho j w :=
      congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S core.toNamedScheduleWellFormed
        (t + 1)) w
    have hij : i ≤ j := by
      dsimp only [i, j]
      exact strict_lengths_mono rho hstartEnd
    have hstartStable : Block.Preceq P
        (Protocol.get_stable (NamedRun.stateBeforeTime S rho start w).st.core) := by
      have hh := (hout w hw (b1 + S.E.Δ) hb0cap le_rfl hcapHor).1
      dsimp only [start]
      simpa only [← readAt_eq_succ] using hh
    have hhold : Block.Preceq P (NamedRun.stateBefore S rho i w).st.core.F ∨
        Block.Preceq P (NamedRun.stateBefore S rho i w).st.core.latest_stable := by
      rw [← hi]
      unfold Protocol.get_stable at hstartStable
      split at hstartStable
      · exact Or.inr hstartStable
      · exact Or.inl hstartStable
    have hcases := stateBefore_stable_covered_of_comparable S rho w i j hij hhold
      (fun k u hik hkj he hpos hcut G hG hlat => by
        have huStart : start ≤ u := Proofs.Optimistic.le_time_of_index_ge S
          core.toNamedScheduleWellFormed (t := start) (j := k) hik he
        have huEnd : u < t + 1 := by
          have hins := Proofs.Optimistic.filter_true_of_index_lt S core.toNamedScheduleWellFormed
            (fun e => decide (e.time < t + 1)) (Proofs.Optimistic.downward_lt (t + 1)) hkj he
          simpa only [decide_eq_true_eq, NamedEvent.time] using hins
        have hut : u ≤ t := Int.lt_add_one_iff.mp huEnd
        have hb0u : b0 < u := by
          dsimp only [start] at huStart
          exact lt_of_le_of_lt hb0cap (lt_of_lt_of_le
            (Int.lt_add_one_iff.mpr le_rfl) huStart)
        have hu0 : (0 : Time) ≤ u :=
          hsix0.trans ((six_delta_lt_b0 S s b0 hmargin).le.trans hb0u.le)
        let qu := clockRoundAt S u
        have hopenU : opening S.E S.hc qu < u := opening_lt_support_cutoff S u hu0 hcut
        have hnextU : u < opening S.E S.hc (qu + 1) := clockRound_lt_opening_succ S u
        have hqu : 0 < qu :=
          Nat.lt_of_lt_of_le (Nat.succ_pos s) (succ_le_clockRound S s b0 u hmargin hb0u.le)
        have hdomU : domain S.E S.hc qu .g2 ≤ u :=
          (domain_le_opening S qu).trans hopenU.le
        have hstopU := support_cutoff_lt_next_domain S qu u hu0 hcut hnextU
        have hquHor : domain S.E S.hc qu .g1 ≤ rho.horizon := by
          rw [domain_g1_eq_opening]
          exact hopenU.le.trans (hut.trans hhor)
        have hb0pred : b0 ≤ u - 1 := Int.le_sub_one_iff.mpr hb0u
        have hupred : u - 1 ≤ rho.horizon :=
          (Int.sub_le_self u (by norm_num)).trans (hut.trans hhor)
        have hmem0 := hK6all (u - 1) hb0pred hupred w hw
        have hpredSucc : u - 1 + 1 = u := by ring
        rw [readAt_eq_succ, hpredSucc] at hmem0
        have hbefore := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S
          core.toNamedScheduleWellFormed he
        change NamedRun.stateBefore S rho k w =
          NamedRun.stateBeforeTime S rho u w at hbefore
        have hread : NamedActionReads.confirmationReadFrom S
            (NamedRun.stateBefore S rho k w) u =
            NamedActionReads.confirmationReadAt S rho w u := by
          rw [hbefore]
          rfl
        have hG' : dutyStableRoot S
            (NamedActionReads.confirmationReadAt S rho w u) = some G := by
          rw [← hread]
          exact hG
        by_cases hquTransition : qu ≤ r0
        · have hcapPred : b1 + S.E.Δ ≤ u - 1 := by
            apply Int.le_sub_one_iff.mpr
            dsimp only [start] at huStart
            exact Int.add_one_le_iff.mp huStart
          have hstrictFloor : ∀ A,
              activeG2 S (NamedRun.readAt S rho (u - 1) w) = some A →
                Block.Preceq P A := by
            by_cases hpredCap : u - 1 ≤ b1 + S.E.Δ
            · exact (hout w hw (u - 1) hb0pred hpredCap hupred).2.1
            · have hqPred : clockRoundAt S (u - 1) ≤ r0 :=
                (clockRoundAt_mono S (Int.sub_le_self u (by norm_num))).trans
                  hquTransition
              exact (htransition w hw (u - 1) (lt_of_not_ge hpredCap)
                hb0pred hqPred hupred).2.1
          have heq := prepared_outputs_eq_strict S rho core w hw qu hqu u
            hu0 rfl hcut (hut.trans hhor)
          rw [dutyStableRoot_eq_activeG2] at hG'
          cases hactive : activeG2 S
              (NamedActionReads.confirmationReadAt S rho w u) with
          | none =>
              rw [hactive] at hG'
              rcases hmem0 with hroot | htree
              · left
                rw [← Option.some.inj hG']
                simpa only [NamedActionReads.confirmationReadAt,
                  NamedActionReads.confirmationReadFrom] using hroot
              · right
                rw [← Option.some.inj hG']
                have hfg := Proofs.Records.preceq_get_fg_root_of_mem_filtered htree
                change Block.Preceq
                  (Protocol.get_fg_root
                    (confirmationReadAt S rho w u).st.core.toHealing.toFG) P
                rw [prepared_root_eq]
                exact hfg
          | some A =>
              rw [hactive] at hG'
              left
              rw [← Option.some.inj hG']
              have hstrictA : activeG2 S (NamedRun.readAt S rho (u - 1) w) =
                  some A := by
                rw [← heq.1]
                exact hactive
              exact hstrictFloor A hstrictA
        · have hrootU : Block.Preceq P
              (NamedRun.stateBeforeTime S rho
                (domain S.E S.hc qu .g2) w).st.core.F ∨
              ∃ R, postOutageFrozenG2At S rho w qu = some R ∧
                Block.Preceq P R := by
            simpa only [postOutageReadAt, Proofs.HealingSurface.relativeG2Read,
              Internal.PhaseGrades.readAt] using
                (hpost qu (Nat.lt_of_not_ge hquTransition) hqu hquHor).1.1 w hw
          exact Or.inl (confirmationDutyRoot_covers S rho P qu core w hw hqu u
            rfl (lt_of_le_of_lt (domain_le_opening S qu) hopenU) hnextU.le
            (hdomU.trans (hut.trans hhor)) hrootU hmem0 hG'))
    have hPtree := hc t hb0 hhor
    have hcompat : Block.compatible P
        (NamedRun.stateBeforeTime S rho (t + 1) w).st.core.F = true := by
      rcases hPtree with hroot | htree
      · have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
          S rho (t + 1) w
        have hFroot := Proofs.Records.preceq_get_fg_root_of_F
          (st := (NamedRun.stateBeforeTime S rho (t + 1) w).st.core.toHealing.toFG)
          (by simpa only [Protocol.Store.toHealing] using hFJ)
        have hroot' : Block.Preceq P
            (Protocol.get_fg_root
              (NamedRun.stateBeforeTime S rho (t + 1) w).st.core.toHealing.toFG) := by
          simpa only [readAt_eq_succ] using hroot
        exact Block.compatible_of_preceq_common hroot' hFroot
      · have hFleP := q10_filtered_F htree
        have hFleP' : Block.Preceq
            (NamedRun.stateBeforeTime S rho (t + 1) w).st.core.F P := by
          simpa only [readAt_eq_succ, Protocol.Store.toHealing] using hFleP
        simp only [Block.compatible, Bool.or_eq_true]
        exact Or.inr hFleP'
    rw [readAt_eq_succ, hj]
    rw [hj] at hcompat
    rcases hcases with hF | hstable
    · unfold Protocol.get_stable
      split
      · exact Block.preceq_trans hF (by assumption)
      · exact hF
    · exact preceq_get_stable _ hstable hcompat
  · intro u hu0 hut B hB
    by_cases hucap : u ≤ b1 + S.E.Δ
    · exact (hout w hw (b1 + S.E.Δ) hb0cap le_rfl hcapHor).2.2
        u hu0 hucap B hB
    obtain ⟨i, he, hpos, hcut, hcand⟩ := hB
    have huHor : u ≤ rho.horizon := hut.trans hhor
    have huNonneg : (0 : Time) ≤ u :=
      hsix0.trans ((six_delta_lt_b0 S s b0 hmargin).le.trans hu0)
    let qu := clockRoundAt S u
    have hopenU : opening S.E S.hc qu < u := opening_lt_support_cutoff S u huNonneg hcut
    have hnextU : u < opening S.E S.hc (qu + 1) := clockRound_lt_opening_succ S u
    have hqu : 0 < qu :=
      Nat.lt_of_lt_of_le (Nat.succ_pos s) (succ_le_clockRound S s b0 u hmargin hu0)
    have hb0u : b0 < u := hb0cap.trans_lt (lt_of_not_ge hucap)
    have hb0pred : b0 ≤ u - 1 := Int.le_sub_one_iff.mpr hb0u
    have hupred : u - 1 ≤ rho.horizon :=
      (Int.sub_le_self u (by norm_num)).trans huHor
    have hpred0 : (0 : Time) ≤ u - 1 :=
      (base_opening_nonneg S qu).trans (Int.le_sub_one_iff.mpr hopenU)
    have hpredNext : u - 1 < opening S.E S.hc (qu + 1) :=
      (Int.sub_le_self u (by norm_num)).trans_lt hnextU
    have hquHor : domain S.E S.hc qu .g1 ≤ rho.horizon := by
      rw [domain_g1_eq_opening]
      exact hopenU.le.trans huHor
    by_cases hquTransition : qu ≤ r0
    · exact (htransition w hw u (lt_of_not_ge hucap) hu0
        hquTransition huHor).2.2 u hu0 le_rfl B
          ⟨i, he, hpos, hcut, hcand⟩
    have hfloorsU := output_floors_at_read S rho P qu core
      (hpost qu (Nat.lt_of_not_ge hquTransition) hqu hquHor).1 w hw
      (u - 1) hpred0 hqu
      (Int.le_sub_one_iff.mpr hopenU) hpredNext hupred
      (hK6all (u - 1) hb0pred hupred w hw)
    have heq := prepared_outputs_eq_strict S rho core w hw qu hqu u huNonneg
      rfl hcut huHor
    have hsg : Block.Preceq P
        (sgRoot S (NamedActionReads.confirmationReadAt S rho w u)) := by
      rw [heq.2]
      exact hfloorsU.2
    have hg2 : ∀ G, activeG2 S
        (NamedActionReads.confirmationReadAt S rho w u) = some G → Block.Preceq P G := by
      rw [heq.1]
      exact hfloorsU.1
    have hread : NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBefore S rho i w) u =
        NamedActionReads.confirmationReadAt S rho w u := by
      have hbefore := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S
        core.toNamedScheduleWellFormed he
      have hbefore' : NamedRun.stateBefore S rho i w =
          NamedRun.stateBeforeTime S rho u w := by
        simpa only using hbefore
      rw [NamedActionReads.confirmationReadAt, hbefore']
    have hcand' : confirmationCandidate S
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBefore S rho i w) u) (S.E.slotOf u - 1) = some B := by
      simpa only [Internal.NamedOutageEntry.confirmationReadFrom] using hcand
    rw [hread] at hcand'
    exact candidate_covers S _ _ hcand' hsg hg2



/-- The relay deadline of a round that acts at or after GST. Recovery plays no
part: after GST every honest send reaches every honest reader within `Δ`, and
one round action is more than `Δ` before the next G2 early cutoff. -/
theorem action_deadline_le_next_earlyG2_of_gst
    (S : Setup V) (r : Round) (hgst : S.E.t_GST ≤ S.a r) :
    max (S.a r) S.E.t_GST + S.E.Δ ≤ early S.E S.hc (r + 1) .g2 := by
  rw [max_eq_left hgst]
  exact healthyAction_add_delta_le_next_earlyG2 S r


































#print axioms firstHealthyAction_exists
#print axioms healthyAction_add_delta_le_next_earlyG2
#print axioms preBoundary_emitted_sg_at_next_g2
#print axioms honestRoundVoter_emits
#print axioms honest_emitted_round_confirmed
#print axioms carriersAbove_of_postOutageAbove
#print axioms carriersAbove_of_sg_clause
#print axioms carriersAbove_of_roundInvariant
#print axioms confirmationDutyRoot_comparable_of_sg_clause
#print axioms honest_rawInput_is_own_round_vote
#print axioms finalized_preceq_of_stable_caseB
#print axioms honestRoundVote_interpreted_at_g1_reader
#print axioms honest_rawView_clean
#print axioms honestRoundVoters_positive_at_g2_read
#print axioms honestRoundVoters_positive_at_g2_read_of_floor
#print axioms honestRoundVoters_positive_at_g1_read
#print axioms opposing_at_g2_read_subset
#print axioms opposing_at_g2_read_subset_of_floor
#print axioms opposing_at_g1_read_subset
#print axioms domain_g1_le_next_domain_g2
#print axioms clause_at_reader_of_carriersAbove
#print axioms clauses_at_reader_of_carriersAbove_of_outageExecution
#print axioms postOutageAbove_of_seed'
#print axioms postOutageAbove_succ_concrete_of_outageExecution
#print axioms postOutageAbove_induction_from_seed'
#print axioms stable_above_P_through_horizon_of_root
#print axioms postOutageAbove_of_seed_truncated
#print axioms postOutageAbove_induction_through_horizon_from_seed_of_outageExecution'
#print axioms output_floors_at_read
#print axioms confirmationDutyRoot_covers
#print axioms prepared_outputs_eq_strict
#print axioms stableUserOutputs_transition_of_sg
#print axioms stableUserOutputsFrom_of_induction
#print axioms postOutageAboveTruncated_after_transition
#print axioms honestRoundVote_interpreted_at_g2_reader_of_deadline
#print axioms honestRoundVoters_positive_at_g2_read_of_deadline
#print axioms opposing_at_g2_read_subset_of_deadline
#print axioms clause_at_g2_of_deadline
#print axioms opening_sg_clause_of_g2_clause
#print axioms postOutageSeedAt_of_sg_clause
#print axioms action_deadline_le_next_earlyG2_of_gst





end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
