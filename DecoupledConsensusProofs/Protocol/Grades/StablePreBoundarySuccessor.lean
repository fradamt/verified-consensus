module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.StableOpeningCarrierFloor
public import DecoupledConsensusProofs.Execution.EarlyHolding
public import DecoupledConsensusProofs.Execution.OutputSeedCore

@[expose] public section

/-!
# Pre-boundary stable-carrier successor

This module is additive. It proves the later-round carrier step from the
healthy-prefix transport, the available prefix no-conflict clause, and the
grade-forming majority. The older byte-exact declaration remains in its Open
record in `OutageResilienceRepairsRun.lean`.
-/



namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Internal.NamedOutageEntry Internal.NamedStableChainOutage
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A round-`r` honest carrier is an interpreted input at a round-`r+1` G2
reader when that reader's finalized root is below the protected prefix. -/
private theorem preBoundary_carrier_interpreted_at_g2_of_finalizedFloor
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1) (P : Block V) (r : Round)
    (hpre : S.a (r + 1) < b0)
    (hcarriers : HonestCarriersAbove S rho P r)
    (w : V) (hw : w ∈ rho.honest)
    (hhor : domain S.E S.hc (r + 1) .g2 ≤ rho.horizon)
    (hFP : Block.Preceq
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core.F P)
    {u : V} (hu : u ∈ honestRoundVoters S rho r) :
    ∃ y ∈ interpretedInputs
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g2) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g2) w).st.core.F
        S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) .g2) u,
      y.round = r ∧
      y.confirmed = some (actionSGBlockAt S rho u r).root ∧
      Block.find?
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g2) w).st.core.T
        (actionSGBlockAt S rho u r).root = some (actionSGBlockAt S rho u r) := by
  have huHon : u ∈ rho.honest :=
    ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u r).mp hu).1
  obtain ⟨a, haround, hval, hemit⟩ := honestRoundVoter_emits S rho hu
  have hactionHor : S.a r ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_succ r)).trans
      (hpre.le.trans (hexec.interval.2.1.trans hexec.interval.2.2))
  have haconfirmed := honest_emitted_round_confirmed S rho hexec.core
    u huHon r hactionHor haround hemit
  obtain ⟨i, hi, _, hbody⟩ := Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
  dsimp at hbody
  obtain ⟨K, hKstaged, haK⟩ := hbody
  have hKindex : K ∈ (NamedRun.stateBefore S rho i u).st.bodies := hKstaged
  have hstate := NamedActionSources.action_read_index S rho
    hexec.core.toNamedScheduleWellFormed i u r hi
  have hKsource : K ∈
      (NamedRun.stateBeforeTime S rho (S.a r) u).st.bodies := by
    rw [← hstate]
    exact hKindex
  let H := actionSGBlockAt S rho u r
  have hcarrierMem : H ∈
      (NamedRun.stateBeforeTime S rho (S.a r) u).st.core.T :=
    actionSGBlockAt_mem_storeBeforeTime S rho u r
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho (S.a r) u hcarrierMem
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
    S rho hexec.core.sorted (S.a r)
  have hDprefix : D ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hDbody
  have hKprefix : K ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hKsource
  have hDrun : NamedRun.blockInRun S rho D :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S huHon hDprefix
  have hKrun : NamedRun.blockInRun S rho K :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S huHon hKprefix
  have hDKroot : D.root = K.root := by
    rw [← Proofs.NamedWire.erase_root D, hDerase]
    exact Option.some.inj (haconfirmed.symm.trans haK)
  have hDK : D = K :=
    hexec.core.toNamedRootCollisionFree.root_injective D K hDrun hKrun D K
      (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self K)) hDKroot
  have hKerased : K.erase = H := by
    rw [← hDK, hDerase]
  let target := NamedRun.stateBeforeTime S rho (domain S.E S.hc (r + 1) .g2) w
  have hFK : Block.Preceq target.st.core.F K.erase := by
    rw [hKerased]
    exact Block.preceq_trans hFP (hcarriers u hu)
  have hdeadline : S.a r + S.E.Δ ≤ early S.E S.hc (r + 1) .g2 :=
    action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r)
  have hearlyCap : early S.E S.hc (r + 1) .g2 ≤ b0 :=
    (early_le_domain S (r + 1)).trans
      ((FrameForward.domain_le_a S (r + 1) .g2).trans hpre.le)
  obtain ⟨_, hstamp, hfind⟩ :=
    NamedHealthyHeadReady.healthy_head_body_at_read
      S rho hexec.core b0 hexec.healthy u huHon w hw K
      (S.a r) (early S.E S.hc (r + 1) .g2)
      (domain S.E S.hc (r + 1) .g2) hKsource hdeadline
      (early_le_domain S (r + 1)) hearlyCap hFK
  have hem : NamedRun.emits S rho a.val_index (.attest a) (S.a a.round) := by
    simpa only [hval, haround] using hemit
  have haHon : a.val_index ∈ rho.honest := by simpa only [hval] using huHon
  obtain ⟨_, _, hraw⟩ := preBoundary_emitted_sg_at_next_g2
    S rho b0 b1 hexec haHon hem (by simpa only [haround] using
      (Assembly.a_mono S (Nat.le_succ r) |>.trans_lt hpre)) w hw
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
  refine ⟨Protocol.sgVote a.erase, Finset.mem_filter.mpr ⟨?_, hready⟩, ?_⟩
  · simpa only [target, haround, hval] using hraw
  refine ⟨?_, ?_, ?_⟩
  · simpa only [sgVote_round, haround]
  · rw [sgVote_confirmed, haconfirmed]
  · simpa only [target, hKerased, Proofs.NamedWire.erase_root] using hfind

/-- Domain-bounded twin of
`preBoundary_carrier_interpreted_at_g2_of_finalizedFloor`. The proof only
needs the next G2 domain inside the healthy prefix; the later round action can
already be at or after the outage boundary. -/
private theorem preBoundary_carrier_interpreted_at_g2_of_domain
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1) (P : Block V) (r : Round)
    (hdomain : domain S.E S.hc (r + 1) .g2 < b0)
    (hcarriers : HonestCarriersAbove S rho P r)
    (w : V) (hw : w ∈ rho.honest)
    (hhor : domain S.E S.hc (r + 1) .g2 ≤ rho.horizon)
    (hFP : Block.Preceq
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core.F P)
    {u : V} (hu : u ∈ honestRoundVoters S rho r) :
    ∃ y ∈ interpretedInputs
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g2) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g2) w).st.core.F
        S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) .g2) u,
      y.round = r ∧
      y.confirmed = some (actionSGBlockAt S rho u r).root ∧
      Block.find?
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g2) w).st.core.T
        (actionSGBlockAt S rho u r).root = some (actionSGBlockAt S rho u r) := by
  have huHon : u ∈ rho.honest :=
    ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u r).mp hu).1
  obtain ⟨a, haround, hval, hemit⟩ := honestRoundVoter_emits S rho hu
  have hactionDomain : S.a r < domain S.E S.hc (r + 1) .g2 :=
    (lt_add_of_pos_right (S.a r) S.E.Δ_pos).trans_le
      ((action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r)).trans
        (early_le_domain S (r + 1)))
  have hactionHor : S.a r ≤ rho.horizon := hactionDomain.le.trans hhor
  have haconfirmed := honest_emitted_round_confirmed S rho hexec.core
    u huHon r hactionHor haround hemit
  obtain ⟨i, hi, _, hbody⟩ := Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
  dsimp at hbody
  obtain ⟨K, hKstaged, haK⟩ := hbody
  have hKindex : K ∈ (NamedRun.stateBefore S rho i u).st.bodies := hKstaged
  have hstate := NamedActionSources.action_read_index S rho
    hexec.core.toNamedScheduleWellFormed i u r hi
  have hKsource : K ∈
      (NamedRun.stateBeforeTime S rho (S.a r) u).st.bodies := by
    rw [← hstate]
    exact hKindex
  let H := actionSGBlockAt S rho u r
  have hcarrierMem : H ∈
      (NamedRun.stateBeforeTime S rho (S.a r) u).st.core.T :=
    actionSGBlockAt_mem_storeBeforeTime S rho u r
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho (S.a r) u hcarrierMem
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
    S rho hexec.core.sorted (S.a r)
  have hDprefix : D ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hDbody
  have hKprefix : K ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hKsource
  have hDrun : NamedRun.blockInRun S rho D :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S huHon hDprefix
  have hKrun : NamedRun.blockInRun S rho K :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S huHon hKprefix
  have hDKroot : D.root = K.root := by
    rw [← Proofs.NamedWire.erase_root D, hDerase]
    exact Option.some.inj (haconfirmed.symm.trans haK)
  have hDK : D = K :=
    hexec.core.toNamedRootCollisionFree.root_injective D K hDrun hKrun D K
      (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self K)) hDKroot
  have hKerased : K.erase = H := by
    rw [← hDK, hDerase]
  let target := NamedRun.stateBeforeTime S rho (domain S.E S.hc (r + 1) .g2) w
  have hFK : Block.Preceq target.st.core.F K.erase := by
    rw [hKerased]
    exact Block.preceq_trans hFP (hcarriers u hu)
  have hdeadline : S.a r + S.E.Δ ≤ early S.E S.hc (r + 1) .g2 :=
    action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r)
  have hearlyCap : early S.E S.hc (r + 1) .g2 ≤ b0 :=
    (early_le_domain S (r + 1)).trans hdomain.le
  obtain ⟨_, hstamp, hfind⟩ :=
    NamedHealthyHeadReady.healthy_head_body_at_read
      S rho hexec.core b0 hexec.healthy u huHon w hw K
      (S.a r) (early S.E S.hc (r + 1) .g2)
      (domain S.E S.hc (r + 1) .g2) hKsource hdeadline
      (early_le_domain S (r + 1)) hearlyCap hFK
  have hem : NamedRun.emits S rho a.val_index (.attest a) (S.a a.round) := by
    simpa only [hval, haround] using hemit
  have haHon : a.val_index ∈ rho.honest := by simpa only [hval] using huHon
  obtain ⟨_, _, hraw⟩ := preBoundary_emitted_sg_at_next_g2
    S rho b0 b1 hexec haHon hem (by
      simpa only [haround] using hactionDomain.trans hdomain) w hw
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
  refine ⟨Protocol.sgVote a.erase, Finset.mem_filter.mpr ⟨?_, hready⟩, ?_⟩
  · simpa only [target, haround, hval] using hraw
  refine ⟨?_, ?_, ?_⟩
  · simpa only [sgVote_round, haround]
  · rw [sgVote_confirmed, haconfirmed]
  · simpa only [target, hKerased, Proofs.NamedWire.erase_root] using hfind

/-- The positive set induced by a pointwise carrier window. -/
private theorem carrierWindow_positive
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (P : Block V) (r : Round) (w : V) (hw : w ∈ rho.honest)
    (hcarriers : HonestCarriersAbove S rho P r)
    (hwindow : ∀ u ∈ honestRoundVoters S rho r,
      ∃ y ∈ interpretedInputs
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) .g2) w).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) .g2) w).st.core.F
          S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) .g2) u,
        y.round = r ∧ y.confirmed = some (actionSGBlockAt S rho u r).root ∧
        Block.find?
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) .g2) w).st.core.T
          (actionSGBlockAt S rho u r).root = some (actionSGBlockAt S rho u r)) :
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
  obtain ⟨y, hy, hyround, hyconfirmed, hyfind⟩ := hwindow u hu
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ u, ?_⟩
  simp only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq]
  refine ⟨DecoupledConsensusModel.Protocol.token y, Finset.mem_image_of_mem _ hy, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have hzraw := (Finset.mem_filter.mp hz).1
    obtain ⟨_, _, _, _, _, _, _, _, hzupper⟩ :=
      honest_rawInput_is_own_round_vote S rho core
        (domain S.E S.hc (r + 1) .g2) (early S.E S.hc (r + 1) .g2)
        w hw huHon hzraw
    simpa only [DecoupledConsensusModel.Protocol.token, hyround] using hzupper
  · change Protocol.head_covers
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core.T P y.confirmed = true
    rw [hyconfirmed]
    simp only [Protocol.head_covers, hyfind]
    exact hcarriers u hu
  · exact honest_rawView_clean S rho core
      (domain S.E S.hc (r + 1) .g2) (late S.E S.hc (r + 1) .g2)
      w hw huHon r (DecoupledConsensusModel.Protocol.token y).round
  · intro x hx hlt
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have hzraw := (Finset.mem_filter.mp hz).1
    obtain ⟨_, _, _, _, _, _, _, _, hzupper⟩ :=
      honest_rawInput_is_own_round_vote S rho core
        (domain S.E S.hc (r + 1) .g2) (late S.E S.hc (r + 1) .g2)
        w hw huHon hzraw
    exact False.elim ((Nat.not_lt_of_ge hzupper) (by
      simpa only [DecoupledConsensusModel.Protocol.token, hyround] using hlt))

/-- Honest G2 opponents are stale when the current honest carrier window is
present. -/
private theorem carrierWindow_opposing
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (P : Block V) (r : Round) (w : V) (hw : w ∈ rho.honest)
    (hcarriers : HonestCarriersAbove S rho P r)
    (hwindow : ∀ u ∈ honestRoundVoters S rho r,
      ∃ y ∈ interpretedInputs
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) .g2) w).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) .g2) w).st.core.F
          S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) .g2) u,
        y.round = r ∧ y.confirmed = some (actionSGBlockAt S rho u r).root ∧
        Block.find?
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) .g2) w).st.core.T
          (actionSGBlockAt S rho u r).root = some (actionSGBlockAt S rho u r)) :
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
        honest_rawInput_is_own_round_vote S rho core
          (domain S.E S.hc (r + 1) .g2) (late S.E S.hc (r + 1) .g2)
          w hw huHon hzraw
      have hlatest : z.round ∈ Protocol.latest_window S.hc.η_SG (r + 1) :=
        mem_latest_window hlower (Nat.lt_succ_of_le hupper)
      by_cases hvote : u ∈ honestRoundVoters S rho r
      · obtain ⟨earlyVote, hearly, hearlyRound, _, hfind⟩ := hwindow u hvote
        have hrz : r ≤ z.round := by
          simpa only [DecoupledConsensusModel.Protocol.token, hearlyRound] using
            hdom (DecoupledConsensusModel.Protocol.token earlyVote)
              (Finset.mem_image_of_mem DecoupledConsensusModel.Protocol.token hearly)
        have hzround : z.round = r := Nat.le_antisymm hupper hrz
        have har : a.round = r := haround.trans hzround
        have hemr : NamedRun.emits S rho u (.attest a) (S.a r) := by
          simpa only [hzround] using hemit
        obtain ⟨j, hj, -⟩ := (show NamedRun.emits S rho u (.attest a) (S.a r) from hemr)
        have hrHor : S.a r ≤ rho.horizon := by
          have h := core.toNamedScheduleWellFormed.in_horizon
            (.tick u (S.a r)) (List.mem_of_getElem? hj)
          simpa only [NamedEvent.time] using h.2
        have haconfirmed := honest_emitted_round_confirmed S rho core
          u huHon r hrHor har hemr
        exact False.elim (hnotcover (by
          change Protocol.head_covers
            (NamedRun.stateBeforeTime S rho
              (domain S.E S.hc (r + 1) .g2) w).st.core.T P z.confirmed = true
          rw [hconfirmed, haconfirmed]
          simp only [Protocol.head_covers, hfind]
          exact hcarriers u hvote))
      · have hzvote : u ∈ honestRoundVoters S rho z.round :=
          (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u z.round).mpr
            ⟨huHon, a, hval, haround, hemit⟩
        have hnotPrevious : u ∉ honestRoundVoters S rho (r + 1 - 1) := by
          simpa only [Nat.add_sub_cancel] using hvote
        exact Proofs.NamedOutageInputs.stale_of_eligible_vote S rho
          hlatest hzvote hnotPrevious
    · have hclean := honest_rawView_clean S rho core
        (domain S.E S.hc (r + 1) .g2) (late S.E S.hc (r + 1) .g2)
        w hw huHon r 0
      exact False.elim (hkey (hclean x hx y hy (Nat.zero_le _) hround))
  · exact Finset.mem_union_left _
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, huHon⟩)

/-- The S7 re-grading step at the exact G2 domain. Unlike the action-carrier
successor, this form only asks that the G2 domain itself is before `b0`. -/
theorem storeGrade_g2_of_honestCarriers_before_boundary_domain
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (r : Round) (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (hforming : GradeFormingThroughout S rho)
    (hdomain : domain S.E S.hc (r + 1) .g2 < b0)
    (hcarriers : HonestCarriersAbove S rho P r)
    (w : V) (hw : w ∈ rho.honest)
    (hFP : Block.Preceq
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core.F P) :
    storeGrade S.E S.hc
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st (r + 1) .g2 P = true := by
  have hcap : b0 ≤ rho.horizon := hexec.interval.2.1.trans hexec.interval.2.2
  have hhor : domain S.E S.hc (r + 1) .g2 ≤ rho.horizon :=
    hdomain.le.trans hcap
  have hroundPos : 0 < r + 1 := Nat.succ_pos r
  have hdomainNonneg : (0 : Time) ≤ domain S.E S.hc (r + 1) .g2 := by
    have hnat : (2 : Nat) ≤ (r + 1) * S.hc.R := by
      have hmul : (1 : Nat) * S.hc.R ≤ (r + 1) * S.hc.R :=
        Nat.mul_le_mul_right S.hc.R hroundPos
      rw [one_mul] at hmul
      exact S.hc.R_ge_two.trans hmul
    have hcast : (2 : Time) ≤ ((((r + 1) * S.hc.R : Nat)) : Time) := by
      exact_mod_cast hnat
    unfold domain opening Protocol.proposal_time Env.t
      Protocol.HealConfig.opening_slot slotStart
    simp only [Phase.domainOffset]
    push_cast
    nlinarith [S.E.Δ_pos]
  have hcovered : RoundCovered S rho (r + 1) :=
    Or.inr ⟨.g2, hdomainNonneg, hhor⟩
  have hmajority : GradeFormingMajority S rho (r + 1) :=
    hforming (r + 1) hroundPos hcovered
  have hwindow (u : V) (hu : u ∈ honestRoundVoters S rho r) :=
    preBoundary_carrier_interpreted_at_g2_of_domain
      S rho b0 b1 hexec P r hdomain hcarriers w hw hhor hFP hu
  have hpositive := carrierWindow_positive
    S rho hexec.core P r w hw hcarriers hwindow
  have hopposing := carrierWindow_opposing
    S rho hexec.core P r w hw hcarriers hwindow
  have hgrade := phaseGrade_of_gradeFormingMajority S rho (r + 1)
    (NamedRun.stateBeforeTime S rho
      (domain S.E S.hc (r + 1) .g2) w).st.core.toHealing.gradeView
    (NamedRun.stateBeforeTime S rho
      (domain S.E S.hc (r + 1) .g2) w).st.core.F P
    (early S.E S.hc (r + 1) .g2) (late S.E S.hc (r + 1) .g2)
    hmajority (by simpa only [Nat.add_sub_cancel] using hpositive) hopposing
  simpa only [storeGrade, phaseGrade, PhaseGrades.readAt] using hgrade

#print axioms storeGrade_g2_of_honestCarriers_before_boundary_domain

/-- The action-Q2 bridge with only processed-tree membership at the G2 domain.
The existing bridge uses its stronger filtered-tree premise only for this
membership fact. -/
private theorem preceq_actionQ2_of_domainGrade_mem
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} (hr : 0 < r)
    (hhor : S.a r ≤ rho.horizon) {C : Block V}
    (hmem : C ∈ (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.T)
    (hgrade : storeGrade S.E S.hc
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st r .g2 C = true)
    (hactive : C ∈ filteredTree (Proofs.HealingSurface.actionReadAt S rho v r)) :
    ∃ Q, nodeQ2 S (Proofs.HealingSurface.actionReadAt S rho v r) r = some Q ∧
      Block.Preceq C Q := by
  obtain ⟨raw, hfz, hCraw⟩ := q10_freeze_of_graded S.E
    (NamedRun.stateBeforeTime S rho
      (domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
    (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.F
    S.hc.η_SG r (q10_early_le_late S r .g2) hmem hgrade
  have hFC : Block.Preceq (Proofs.HealingSurface.actionReadAt S rho v r).st.core.F C :=
    q10_filtered_F hactive
  have hcompat : Block.compatible C
      (Proofs.HealingSurface.actionReadAt S rho v r).st.core.F = true := by
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr hFC
  have hCclip : Block.Preceq C
      (DecoupledConsensusModel.Protocol.clipGrade raw
        (Proofs.HealingSurface.actionReadAt S rho v r).st.core.F) :=
    (q10_retained_prefix raw
      (Proofs.HealingSurface.actionReadAt S rho v r).st.core.F C hcompat).mpr hCraw
  obtain ⟨Q, hQ, hCQ⟩ := q10_activePrefix_dominates hactive hCclip
  refine ⟨Q, ?_, hCQ⟩
  show DecoupledConsensusModel.Protocol.grade2Block
      (Proofs.HealingSurface.actionReadAt S rho v r).st.core.toHealing
    (DecoupledConsensusModel.Protocol.readFrame (Proofs.HealingSurface.actionReadAt S rho v r).cache
      (Proofs.HealingSurface.actionReadAt S rho v r).st.core.toHealing r) = some Q
  unfold DecoupledConsensusModel.Protocol.grade2Block
  rw [if_pos (actionFrame_allClosed S core hv hr hhor),
    actionFrame_g2 S core hv hr hhor,
    show storeRoot S.E S.hc
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st r .g2 =
        some raw from hfz]
  exact hQ

set_option maxHeartbeats 400000 in
/-- Additive pre-boundary successor. The stable source and prefix no-conflict
are explicit because they supply the named representative and viability used
by the selection action filter. -/
theorem honestCarriersAbove_succ_of_gradeFormingMajority_of_stable
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s r : Round) (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : NamedOutageEntry.SlashableBound S rho)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hseed : OutputSeed S rho b0 s P)
    (hno : NoHonestConflictAbove S rho b0 P)
    (hsr : s ≤ r) (hpre : S.a (r + 1) < b0)
    (hcarriers : HonestCarriersAbove S rho P r) :
    HonestCarriersAbove S rho P (r + 1) := by
  have hcap : b0 ≤ rho.horizon := hexec.interval.2.1.trans hexec.interval.2.2
  have hnextHor : S.a (r + 1) ≤ rho.horizon := hpre.le.trans hcap
  have hdomainCap : domain S.E S.hc (r + 1) .g2 ≤ b0 :=
    (FrameForward.domain_le_a S (r + 1) .g2).trans hpre.le
  have hdomainHor : domain S.E S.hc (r + 1) .g2 ≤ rho.horizon :=
    hdomainCap.trans hcap
  have hcovered : RoundCovered S rho (r + 1) :=
    Or.inl ⟨Proofs.HealingLemmas.a_nonneg S (r + 1), hnextHor⟩
  have hmajority : GradeFormingMajority S rho (r + 1) :=
    hforming (r + 1) (Nat.succ_pos r) hcovered
  have hsourceDeadline : S.a s + S.E.Δ ≤ domain S.E S.hc (r + 1) .g2 := by
    exact (Int.add_le_add_right (Assembly.a_mono S hsr) S.E.Δ).trans
      ((action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r)).trans
        (early_le_domain S (r + 1)))
  obtain ⟨Pn, hPe, hPnrun, hPnDomain⟩ :=
    NamedEarlyHolding.stable_prefix_held_before_boundary_of_seed
      S rho b0 b1 hexec hsleep v hv s P hmargin hseed hno
      (domain S.E S.hc (r + 1) .g2) hsourceDeadline hdomainCap
  have hsourceAction : S.a s + S.E.Δ ≤ S.a (r + 1) :=
    hsourceDeadline.trans (FrameForward.domain_le_a S (r + 1) .g2)
  obtain ⟨Pm, hPme, hPmrun, hPmAction⟩ :=
    NamedEarlyHolding.stable_prefix_held_before_boundary_of_seed
      S rho b0 b1 hexec hsleep v hv s P hmargin hseed hno
      (S.a (r + 1)) hsourceAction hpre.le
  intro u hu
  have huHon : u ∈ rho.honest :=
    ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u (r + 1)).mp hu).1
  let action := Proofs.HealingSurface.actionReadAt S rho u (r + 1)
  by_cases hPF : Block.Preceq P action.st.core.F
  · have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
      S rho (S.a (r + 1)) u
    have hFroot : Block.Preceq action.st.core.F
        (Protocol.get_fg_root action.st.core.toHealing.toFG) := by
      exact Proofs.Records.preceq_get_fg_root_of_F
        (st := action.st.core.toHealing.toFG)
          (by simpa only [action, Proofs.HealingSurface.actionReadAt,
            Internal.NamedOutageEntry.actionReadAt,
            NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
            NamedActionReads.confirmationReadFrom, Protocol.NamedDuties.update_confirmation_with,
            Protocol.update_confirmation_with, Protocol.Store.toHealing] using hFJ)
    exact Block.preceq_trans hPF (Block.preceq_trans hFroot (by
      simpa only [action, Proofs.HealingSurface.actionReadAt] using
        actionFGRoot_preceq_actionSGBlockAt S rho u (r + 1)))
  · obtain ⟨F, -, hFErase, hcompatNamed⟩ :=
      NamedFinalityGuard.finalized_representative_compatible_before_boundary
        S rho b0 b1 s hexec hmargin hsleep Pm hPmrun
          (by simpa only [hPme] using hno) u huHon (S.a (r + 1)) hpre.le
    have hcompat : Block.compatible P action.st.core.F = true := by
      have h := Proofs.NamedWire.erase_compatible hcompatNamed
      rw [hPme, hFErase] at h
      simpa only [action, Proofs.HealingSurface.actionReadAt,
        Internal.NamedOutageEntry.actionReadAt,
        NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedDuties.update_confirmation_with,
        Protocol.update_confirmation_with] using h
    have hFActionP : Block.Preceq action.st.core.F P := by
      simp only [Block.compatible, Bool.or_eq_true] at hcompat
      rcases hcompat with hPF' | hFP
      · exact False.elim (hPF hPF')
      · exact hFP
    have hFDomainAction : Block.Preceq
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g2) u).st.core.F action.st.core.F := by
      dsimp only [action, Proofs.HealingSurface.actionReadAt,
        Internal.NamedOutageEntry.actionReadAt, NamedActionReads.actionReadAt,
        NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
        Protocol.NamedDuties.update_confirmation_with,
        Protocol.update_confirmation_with]
      change Block.Preceq
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g2) u).st.core.F
        (NamedRun.stateBeforeTime S rho (S.a (r + 1)) u).st.core.F
      exact incl_strict_F_mono S rho hexec.core.toNamedScheduleWellFormed u
        (FrameForward.domain_le_a S (r + 1) .g2)
    have hFDomainP := Block.preceq_trans hFDomainAction hFActionP
    have hwindow (x : V) (hx : x ∈ honestRoundVoters S rho r) :=
      preBoundary_carrier_interpreted_at_g2_of_finalizedFloor
        S rho b0 b1 hexec P r hpre hcarriers u huHon hdomainHor hFDomainP
          (u := x) hx
    have hpositive := carrierWindow_positive
      S rho hexec.core P r u huHon hcarriers hwindow
    have hopposing := carrierWindow_opposing
      S rho hexec.core P r u huHon hcarriers hwindow
    have hgradeBool := phaseGrade_of_gradeFormingMajority S rho (r + 1)
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) u).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) u).st.core.F P
      (early S.E S.hc (r + 1) .g2) (late S.E S.hc (r + 1) .g2)
      hmajority (by simpa only [Nat.add_sub_cancel] using hpositive) hopposing
    have hgrade : storeGrade S.E S.hc
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g2) u).st (r + 1) .g2 P = true := by
      simpa only [storeGrade, phaseGrade, PhaseGrades.readAt] using hgradeBool
    have hPtree : P ∈
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g2) u).st.core.T := by
      have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
        (domain S.E S.hc (r + 1) .g2) u).1.1.1
      rw [hcoh.1, ← hPe]
      exact Finset.mem_image_of_mem _ (hPnDomain u huHon)
    have hprotected := NamedFGProtection.fg_protection_of_held_before_boundary
      S rho b0 b1 s hexec hmargin hsleep Pm
        (by simpa only [hPme] using hno) u huHon
        (S.a (r + 1)) hpre.le (hPmAction u huHon)
    rcases hprotected with hProot | hPactive
    · exact Block.preceq_trans (by simpa only [hPme] using hProot)
        (actionFGRoot_preceq_actionSGBlockAt S rho u (r + 1))
    · have hPactive' : P ∈ filteredTree action := by
        simpa only [hPme, action, Proofs.HealingSurface.actionReadAt,
          Internal.NamedOutageEntry.actionReadAt, NamedActionReads.actionReadAt,
          NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
          Protocol.NamedDuties.update_confirmation_with,
          Protocol.update_confirmation_with] using hPactive
      obtain ⟨Q, hQ, hPQ⟩ := preceq_actionQ2_of_domainGrade_mem
        S hexec.core huHon (Nat.succ_pos r) hnextHor hPtree hgrade hPactive'
      exact preceq_actionSGBlockAt_of_actionQ2
        S hexec.core huHon (Nat.succ_pos r) hnextHor hQ hPQ

#print axioms honestCarriersAbove_succ_of_gradeFormingMajority_of_stable

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
