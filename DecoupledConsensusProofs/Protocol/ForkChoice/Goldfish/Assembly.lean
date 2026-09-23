module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.Interpolation
public import DecoupledConsensusProofs.Execution.BoundaryHolding
public import DecoupledConsensusProofs.Objects.FirstCheckpoint
public import DecoupledConsensusProofs.Protocol.Handlers.RetentionNamed
public import DecoupledConsensusProofs.Protocol.Schedule.RecordAtBoundary
public import DecoupledConsensusProofs.Execution.OutputSeedCore

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

set_option linter.unusedSectionVars false

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. The output bridges (L2, L3) on earlier -/

/-- The active G2 candidate is a member of the reader's filtered tree: it is
the `deepest?` of a filter of that tree. -/
theorem activeG2_mem_filtered_tree (S : Setup V) (n : NamedNodeState V) {G : Block V}
    (hG : activeG2 S n = some G) :
    G ∈ Protocol.get_filtered_block_tree n.st.core.toHealing.toFG := by
  rw [activeG2_eq] at hG
  obtain ⟨raw, _, hA⟩ := Option.bind_eq_some_iff.mp hG
  exact NamedProposalParent.activePrefix_mem _ raw G hA

/-- A prefix below the FG root is below the active G2 candidate, because the
candidate is a filtered-tree member and every such member is above the root. -/
theorem preceq_activeG2_of_preceq_fg_root (S : Setup V) (n : NamedNodeState V)
    {P G : Block V}
    (hroot : Block.Preceq P (Protocol.get_fg_root n.st.core.toHealing.toFG))
    (hG : activeG2 S n = some G) : Block.Preceq P G :=
  Block.preceq_trans hroot
    (Proofs.Records.preceq_get_fg_root_of_mem_filtered (activeG2_mem_filtered_tree S n hG))

/-- **L2/L3, conclusion form.** `StableUserOutputs` is `EntryPrefixOutputs`
with the first disjunction turned into a `∀ G`. -/
theorem stableUserOutputs_of_entryPrefixOutputs (S : Setup V) (rho : NamedRun V)
    (b0 b1 : Time) (P : Block V) (h : EntryPrefixOutputs S rho b0 b1 P) :
    StableUserOutputs S rho b0 b1 P := by
  intro w hw t hb0 hcap hhor
  obtain ⟨hfirst, _, hconf, hcand⟩ := h w hw t hb0 hcap hhor
  refine ⟨hconf, ?_, hcand⟩
  intro G hG
  rcases hfirst with hroot | ⟨G', hG', hPG'⟩
  · exact preceq_activeG2_of_preceq_fg_root S _ hroot hG
  · rw [hG'] at hG
    rw [← Option.some_inj.mp hG]
    exact hPG'




/-- If two indices are past the end of the event list, the folds agree. -/
private theorem stateBefore_eq_of_none (S : Setup V) (rho : NamedRun V) {i j : Nat}
    (hnone : rho.events[j]? = none) (hji : j < i) :
    NamedRun.stateBefore S rho i = NamedRun.stateBefore S rho j := by
  have hj : rho.events.length ≤ j := by
    by_contra hc
    exact absurd (List.getElem?_eq_getElem (Nat.lt_of_not_le hc)) (by rw [hnone]; simp)
  unfold NamedRun.stateBefore
  rw [List.take_of_length_le hj, List.take_of_length_le (le_of_lt (lt_of_le_of_lt hj hji))]

/-- **Retention.** The boundary carry survives to every read of the window, in
the shape the confirmation write produces it: finality OR the stable record. The
finality arm rides on `Proofs.NamedRuntime.stateBefore_F_mono` inside the ladder and
consumes no coverage at all. -/
theorem readStableCoverage_of_write_coverage (S : Setup V) (rho : NamedRun V)
    (b0 cap : Time)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (hnodup : rho.events.Nodup)
    (P : Block V) (hcov : StableWriteCoverageWindow S rho b0 cap P)
    (hold : ∀ w ∈ rho.honest,
      Block.Preceq P (NamedRun.stateBeforeTime S rho b0 w).st.core.F ∨
      Block.Preceq P (NamedRun.stateBeforeTime S rho b0 w).st.core.latest_stable) :
    ReadStableCoverage S rho b0 cap P := by
  intro w hw t hb0 hcap hhor
  obtain ⟨i, hi, hi2, hi3⟩ := stateBeforeTime_prefix_index S rho hsorted b0
  obtain ⟨j, hj, hj2, hj3⟩ := stateBeforeTime_prefix_index S rho hsorted (t + 1)
  have hread : NamedRun.readAt S rho t = NamedRun.stateBefore S rho j := by
    rw [readAt_eq_succ, hj]
  have hold' := hold w hw
  rw [hi] at hold'
  rw [hread]
  by_cases hij : i ≤ j
  · refine stateBefore_stable_covered S rho w i j hij hold' ?_
    intro k u hk hkj he hpos hcut
    have hb0u : b0 ≤ u := by
      by_contra hc
      exact absurd (hi3 k _ he (not_le.mp hc)) (not_lt.mpr hk)
    have hut : u ≤ t := Int.lt_add_one_iff.mp (hj2 k _ hkj he)
    have hpre : NamedRun.stateBefore S rho k w = NamedRun.stateBeforeTime S rho u w :=
      Proofs.NamedRuntime.tick_prefix_eq_strict S rho hsorted hnodup he
    rw [hpre]
    exact hcov w hw u hb0u (le_trans hut hcap) (le_trans hut hhor) hpos hcut
  · cases hjn : rho.events[j]? with
    | none =>
        rw [stateBefore_eq_of_none S rho hjn (Nat.lt_of_not_le hij)] at hold'
        exact hold'
    | some e =>
      have hb : e.time < b0 := hi2 j e (Nat.lt_of_not_le hij) hjn
      exact absurd (hj3 j e hjn
        (lt_of_lt_of_le hb (le_trans hb0 (Int.le_add_one (le_refl t))))) (lt_irrefl j)

#print axioms readStableCoverage_of_write_coverage



private theorem asm_succ_le_of_lt : ∀ a b : Int, a < b → a + 1 ≤ b := by
  intro a b h; omega

private theorem asm_nonneg_of_six_lt : ∀ b d : Int, 0 < d → 6 * d < b → 0 ≤ b := by
  intro b d hd h; omega


/-- **The CARRY obligation at a staged support-cutoff read.** `hvia` is L4's own
row at the read, with the finality arm in front, and each of its three arms
discharges the obligation on its own.

* Finality: the record is not needed, the accessor falls back on `F`.
* The FG root already covers `P`: then so does every root the duty could write,
  because 26 put the write's range inside `get_filtered_block_tree`
  (`fgRoot_preceq_dutyStableRoot`). No grade row is used in this arm.
* `P` is in the candidate tree: then the `sg` row carries the frozen G2 root to
  the read (`strict_g2_of_opening`) and to the staged frame
  (`frame_phase_prepared_eq`), `P` is in the projected slice, and
  `activePrefix_covers` puts the write's root above it.

The `sg` row's own finality arm lands back on the first case. -/
theorem stableWriteAt_of_sg (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (w : V) (hw : w ∈ rho.honest)
    (P : Block V) (r : Round) (hr : 0 < r) (u : Time) (hround : clockRoundAt S u = r)
    (hopen : opening S.E S.hc r < u) (hstrict : u ≤ opening S.E S.hc (r + 1))
    (hhor : opening S.E S.hc r ≤ rho.horizon)
    (hsg : Block.Preceq P
        (NamedRun.readAt S rho (domain S.E S.hc r .g1) w).st.core.F ∨
      ∃ raw : Block V,
        (DecoupledConsensusModel.Protocol.readFrame
            (NamedRun.readAt S rho (domain S.E S.hc r .g1) w).cache
            (NamedRun.readAt S rho (domain S.E S.hc r .g1) w).st.core.toHealing r).g2 =
          some (some raw) ∧ Block.Preceq P raw)
    (hcompat : Block.compatible P (NamedRun.stateBeforeTime S rho u w).st.core.F = true)
    (hvia : Block.Preceq P (NamedRun.stateBeforeTime S rho u w).st.core.F ∨
      Block.Preceq P (Protocol.get_fg_root
        (NamedRun.stateBeforeTime S rho u w).st.core.toHealing.toFG) ∨
      P ∈ Protocol.get_filtered_block_tree
        (NamedRun.stateBeforeTime S rho u w).st.core.toHealing.toFG) :
    StableWriteAt S (confirmationReadAt S rho w u) P := by
  -- The FG-root arm needs no grade row at all: every root the duty can write is
  -- at or above the reader's FG root, which already covers `P`.
  rcases hvia with hPF | hRoot | hmem
  · exact Or.inl hPF
  · refine Or.inr (fun G hG => ?_)
    exact Block.preceq_trans hRoot
      (fgRoot_preceq_dutyStableRoot S (confirmationReadAt S rho w u) hG)
  · rcases hsg with hopenF | ⟨raw, hg2, hPraw⟩
    · refine Or.inl ?_
      show Block.Preceq P (NamedRun.stateBeforeTime S rho u w).st.core.F
      rw [readAt_eq_succ, domain_g1_eq_opening] at hopenF
      exact preceq_F_fwd S rho core.toNamedScheduleWellFormed w P _ _
        (asm_succ_le_of_lt _ _ hopen) hopenF
    · obtain ⟨raw', hg2', hPraw'⟩ := strict_g2_of_opening S rho core w hw r hr P u hopen
        hstrict hhor raw hg2 hPraw hcompat
      have hg2p := frame_phase_prepared_eq S rho w r .g2 u hround _ hg2'
      rw [← hround] at hg2p
      obtain ⟨G, hG, hPG⟩ := activePrefix_covers hmem hPraw'
      exact Or.inr (stableWrite_covers S _
        ⟨G, dutyStableRoot_of_frame_of_active S _ hg2p hG, hPG⟩)

#print axioms stableWriteAt_of_sg


/-- **The BASE obligation at a staged support-cutoff read.** The same proof as
the carry's third arm, but it keeps the existential: this is the read where the
write has to FIRE, so the FG-root arm is not enough and `hmem` has to be the
candidate-tree membership itself.

That is the whole of 26's cost on this chain, and it is asked at ONE
read, round `s + 1`'s formation confirmation. -/
theorem stableWriteFiresAt_of_sg (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (w : V) (hw : w ∈ rho.honest)
    (P : Block V) (r : Round) (hr : 0 < r) (u : Time) (hround : clockRoundAt S u = r)
    (hopen : opening S.E S.hc r < u) (hstrict : u ≤ opening S.E S.hc (r + 1))
    (hhor : opening S.E S.hc r ≤ rho.horizon)
    (hsg : Block.Preceq P
        (NamedRun.readAt S rho (domain S.E S.hc r .g1) w).st.core.F ∨
      ∃ raw : Block V,
        (DecoupledConsensusModel.Protocol.readFrame
            (NamedRun.readAt S rho (domain S.E S.hc r .g1) w).cache
            (NamedRun.readAt S rho (domain S.E S.hc r .g1) w).st.core.toHealing r).g2 =
          some (some raw) ∧ Block.Preceq P raw)
    (hcompat : Block.compatible P (NamedRun.stateBeforeTime S rho u w).st.core.F = true)
    (hmem : Block.Preceq P (NamedRun.stateBeforeTime S rho u w).st.core.F ∨
      P ∈ Protocol.get_filtered_block_tree
        (NamedRun.stateBeforeTime S rho u w).st.core.toHealing.toFG ∨
      Block.Preceq P (Protocol.get_fg_root
        (NamedRun.stateBeforeTime S rho u w).st.core.toHealing.toFG)) :
    StableWriteFiresAt S (confirmationReadAt S rho w u) P := by
  rcases hmem with hPF | hmem | hRoot
  · exact Or.inl hPF
  · rcases hsg with hopenF | ⟨raw, hg2, hPraw⟩
    · refine Or.inl ?_
      show Block.Preceq P (NamedRun.stateBeforeTime S rho u w).st.core.F
      rw [readAt_eq_succ, domain_g1_eq_opening] at hopenF
      exact preceq_F_fwd S rho core.toNamedScheduleWellFormed w P _ _
        (asm_succ_le_of_lt _ _ hopen) hopenF
    · obtain ⟨raw', hg2', hPraw'⟩ := strict_g2_of_opening S rho core w hw r hr P u hopen
        hstrict hhor raw hg2 hPraw hcompat
      have hg2p := frame_phase_prepared_eq S rho w r .g2 u hround _ hg2'
      rw [← hround] at hg2p
      obtain ⟨G, hG, hPG⟩ := activePrefix_covers hmem hPraw'
      exact Or.inr ⟨G, dutyStableRoot_of_frame_of_active S _ hg2p hG, hPG⟩
  · obtain ⟨G, hG⟩ := dutyStableRoot_some S (confirmationReadAt S rho w u)
    exact Or.inr ⟨G, hG, Block.preceq_trans hRoot
      (fgRoot_preceq_dutyStableRoot S (confirmationReadAt S rho w u) hG)⟩

#print axioms stableWriteFiresAt_of_sg

/-- The finality guard at a read at or before the boundary, in the compatibility
shape `strict_g2_of_opening` consumes. -/
theorem compat_before_boundary (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (s : Round) (Pn : NamedBlock V) (hexec : OutageExecution S rho b0 b1)
    (hmargin : FormationMargin S s b0) (hsleep : OutageSleepyThroughout S rho)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (w : V) (hw : w ∈ rho.honest) (u : Time) (hu : u ≤ b0) :
    Block.compatible Pn.erase (NamedRun.stateBeforeTime S rho u w).st.core.F = true := by
  obtain ⟨F, _, hFe, hFcompat⟩ :=
    NamedFinalityGuard.finalized_representative_compatible_before_boundary S rho b0 b1 s
      hexec hmargin hsleep Pn hscope hno w hw u hu
  rw [← hFe]
  exact Proofs.NamedWire.erase_compatible hFcompat

#print axioms compat_before_boundary


/-- **L4's row at a pre-boundary read.** The protected prefix is held at every
honest node from round `s`'s action deadline onward, and a held prefix before
the boundary is either past the reader's FG root or inside its candidate tree
(`NamedFGProtection.fg_protection_of_held_before_boundary`). This is the
pre-boundary twin of the row `fg_noninterference_after_boundary` gives inside
the window, and 26's carry obligation is discharged by either arm. -/
theorem fgRow_before_boundary (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (v : V) (s : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho) (hv : v ∈ rho.honest)
    (hseed : OutputSeed S rho b0 s Pn.erase)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (w : V) (hw : w ∈ rho.honest) (u : Time)
    (hopen1 : opening S.E S.hc (s + 1) ≤ u) (hu : u ≤ b0) :
    Block.Preceq Pn.erase (Protocol.get_fg_root
      (NamedRun.stateBeforeTime S rho u w).st.core.toHealing.toFG) ∨
    Pn.erase ∈ Protocol.get_filtered_block_tree
      (NamedRun.stateBeforeTime S rho u w).st.core.toHealing.toFG := by
  have hdead : S.a s + S.E.Δ ≤ u :=
    ((action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self s)).trans
      (early_le_domain S (s + 1))).trans ((domain_le_opening S (s + 1)).trans hopen1)
  obtain ⟨Pk, hPke, _, hPkheld⟩ := NamedEarlyHolding.stable_prefix_held_before_boundary_of_seed
    S rho b0 b1 hexec hsleep v hv s Pn.erase hmargin hseed hno u hdead hu
  have hrow := NamedFGProtection.fg_protection_of_held_before_boundary S rho b0 b1 s
    hexec hmargin hsleep Pk (by rw [hPke]; exact hno) w hw u hu (hPkheld w hw)
  rw [hPke] at hrow
  exact hrow

#print axioms fgRow_before_boundary



/-- **The pre-outage segment of the stable write.** From round `s + 1`'s
formation cutoff to the boundary, the `sg` disjunction is the pre-boundary
frame premise on a round
that acts before the outage and the ladder's own field on the round that
straddles it; the compatibility side condition is the clean-tier finality row. -/
theorem stableWriteCoverageBefore_of_invariant
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V) (s : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho) (hv : v ∈ rho.honest)
    (hseed : OutputSeed S rho b0 s Pn.erase)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hinv : ∀ r : Round, DomainIncluded S rho b0 r → domain S.E S.hc r .g2 ≤ b1 + S.E.Δ →
      RoundInvariant S rho b0 Pn r)
    (hframes : PreBoundaryFrames S rho b0 s Pn.erase) :
    StableWriteCoverageBefore S rho b0 s Pn.erase := by
  intro w hw u hlo hhi hpos hcut
  have hopen1 : opening S.E S.hc (s + 1) ≤ u :=
    (opening_lt_formation S (s + 1)).le.trans hlo
  have hu0 : (0 : Time) ≤ u := (base_opening_nonneg S (s + 1)).trans hopen1
  have hhor : u ≤ rho.horizon :=
    hhi.le.trans (hexec.interval.2.1.trans hexec.interval.2.2)
  have hrpos : 0 < clockRoundAt S u :=
    Nat.lt_of_lt_of_le (Nat.succ_pos s) (succ_le_clockRound_of_opening S (s + 1) u hopen1)
  have hsg := sg_before_boundary S rho b0 b1 s Pn hexec hinv hframes w hw u hlo hhi.le
  have hcompat :=
    compat_before_boundary S rho b0 b1 s Pn hexec hmargin hsleep hscope hno w hw u hhi.le
  
  -- since the read is past round `s`'s action deadline by one delay, and a held
  -- prefix before the boundary is either past the FG root or in the candidate
  -- tree. The carry obligation takes either arm.
  have hvia := fgRow_before_boundary S rho b0 b1 v s Pn hexec hmargin hsleep hv hseed
    hno w hw u hopen1 hhi.le
  exact stableWriteAt_of_sg S rho hexec.core w hw Pn.erase (clockRoundAt S u) hrpos u rfl
    (opening_lt_support_cutoff S u hu0 hcut)
    (le_of_lt (clockRound_lt_opening_succ S u))
    ((opening_le_clockRound S u hu0).trans hhor) hsg hcompat (Or.inr hvia)

#print axioms stableWriteCoverageBefore_of_invariant


/-- **The base write, at round `s + 1`'s formation confirmation.** The one read
where the write has to FIRE, and the only place 26 costs
anything on this chain.

The `sg` row and the finality guard are the pre-boundary segment's, at the
formation cutoff. What is left is the row's SECOND arm at that read: the
protected prefix inside the reader's candidate tree. L4's row
(`fgRow_before_boundary`) gives that arm or the other one, `P ⪯ get_fg_root`,
and the other one does NOT fire: every member of the projected slice is at or
above the FG root, so it covers `P`, but the slice can be EMPTY when the FG root
is a justified block standing above the frozen G2 root — the cascade branch that
 26 chose to let freeze the record.

The first arm splits three ways and only ONE of the three is open.

* Finality has passed the prefix: the write is not needed.
* The FG root is the FINALIZED block (`h_max ≠ h_j + 1`): then it is below the
  prefix by the finality guard, the viability half is
  `viableRow_before_boundary`, and the two compose into membership. CLOSED.
* The FG root is the JUSTIFIED block standing strictly above the prefix: OPEN.

Open (addendum 34, 26 item 3, the FG-root half), in that last
configuration only. Either of two facts closes it, and neither is in the green
tree: `st.J ⪯ Pn.erase` at this read, which with the viability half gives
membership outright; or `st.J ⪯ raw` for the row's frozen root, which puts the
FG root itself in the projected slice (it is in the candidate tree by
`FrameStoreRoot.fgRoot_mem_filtered_of_state_facts` under the store invariants)
and makes the write fire above the FG root, hence above the prefix.

This is exactly the cascade branch 26 chose to let freeze the record, now
read at the one place where freezing is not harmless. The targeted-timeout
argument does not reach it: it settles the VIABILITY half, by showing every
height the maximum reaches has a target extending the prefix, and says nothing
about where the justified checkpoint stands relative to the frozen G2 root. -/
theorem formationStableWrite_of_invariant
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V) (s : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho) (hv : v ∈ rho.honest)
    (hseed : OutputSeed S rho b0 s Pn.erase)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hinv : ∀ r : Round, DomainIncluded S rho b0 r → domain S.E S.hc r .g2 ≤ b1 + S.E.Δ →
      RoundInvariant S rho b0 Pn r)
    (hframes : PreBoundaryFrames S rho b0 s Pn.erase) :
    FormationStableWrite S rho s Pn.erase := by
  intro w hw
  have hhi : formationConfirmationTime S (s + 1) < b0 := formation_lt_boundary S s b0 hmargin
  obtain ⟨hposf, hcutf⟩ := formation_cutoff_slot S s
  have hopen1 : opening S.E S.hc (s + 1) ≤ formationConfirmationTime S (s + 1) :=
    (opening_lt_formation S (s + 1)).le
  have hu0 : (0 : Time) ≤ formationConfirmationTime S (s + 1) :=
    (base_opening_nonneg S (s + 1)).trans hopen1
  have hhor : formationConfirmationTime S (s + 1) ≤ rho.horizon :=
    hhi.le.trans (hexec.interval.2.1.trans hexec.interval.2.2)
  have hrpos : 0 < clockRoundAt S (formationConfirmationTime S (s + 1)) :=
    Nat.lt_of_lt_of_le (Nat.succ_pos s)
      (succ_le_clockRound_of_opening S (s + 1) _ hopen1)
  have hsg := sg_before_boundary S rho b0 b1 s Pn hexec hinv hframes w hw
    (formationConfirmationTime S (s + 1)) le_rfl hhi.le
  have hcompat := compat_before_boundary S rho b0 b1 s Pn hexec hmargin hsleep hscope hno
    w hw (formationConfirmationTime S (s + 1)) hhi.le
  refine stableWriteFiresAt_of_sg S rho hexec.core w hw Pn.erase
    (clockRoundAt S (formationConfirmationTime S (s + 1))) hrpos
    (formationConfirmationTime S (s + 1)) rfl
    (opening_lt_support_cutoff S _ hu0 hcutf)
    (le_of_lt (clockRound_lt_opening_succ S _))
    ((opening_le_clockRound S _ hu0).trans hhor) hsg hcompat ?_
  rcases fgRow_before_boundary S rho b0 b1 v s Pn hexec hmargin hsleep hv hseed hno
    w hw (formationConfirmationTime S (s + 1)) hopen1 hhi.le with hRoot | hmem
  · exact Or.inr (Or.inr hRoot)
  · exact Or.inr (Or.inl hmem)

/-- **The in-window segment of the stable write.** The same two inputs as
`Interpolation.candidateReadCoverage_of_invariant`: the `sg` disjunction at the
read's own clock round and L4's compatibility at the read. -/
theorem stableWriteCoverage_of_invariant
    (S : Setup V) (rho : NamedRun V) (b0 b1 cap : Time) (s : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hmargin : FormationMargin S s b0) (hsleep : OutageSleepyThroughout S rho)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hheld0 : ∀ w ∈ rho.honest, Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hinv : ∀ r : Round, DomainIncluded S rho b0 r → domain S.E S.hc r .g2 ≤ b1 + S.E.Δ →
      RoundInvariant S rho b0 Pn r)
    (hframes : PreBoundaryFrames S rho b0 s Pn.erase)
    (hcapb1 : cap ≤ b1 + S.E.Δ)
    (hanchor : ∀ t : Time, b0 ≤ t → t ≤ cap → t ≤ rho.horizon →
      S.a (clockRoundAt S t) < b0 →
        ∃ r : Round, IntrinsicConflictingCarrierBand S rho Pn r ∧
          IntrinsicHighEntryHistory S rho Pn r ∧ t < S.a r) :
    StableWriteCoverageWindow S rho b0 cap Pn.erase := by
  intro w hw u hb0 hcap hhor hpos hcut
  have hb0pos : 6 * S.E.Δ < b0 := six_delta_lt_b0 S s b0 hmargin
  have hu0 : (0 : Time) ≤ u :=
    (asm_nonneg_of_six_lt _ _ S.E.Δ_pos hb0pos).trans hb0
  have hsg := sg_at_clockRound S rho b0 b1 cap s Pn hmargin hinv hframes hcapb1 w hw u
    hb0 hcap hhor
  have hL4 : Pn ∈ (NamedRun.stateBeforeTime S rho u w).st.bodies ∧
      (Block.Preceq Pn.erase (Protocol.get_fg_root
          (NamedRun.stateBeforeTime S rho u w).st.core.toHealing.toFG) ∨
        Pn.erase ∈ Protocol.get_filtered_block_tree
          (NamedRun.stateBeforeTime S rho u w).st.core.toHealing.toFG) ∧
      Block.compatible Pn.erase (NamedRun.stateBeforeTime S rho u w).st.core.F = true := by
    by_cases hpb : b0 ≤ S.a (clockRoundAt S u)
    · obtain ⟨hinc, hb1r⟩ := domainIncluded_clockRound S rho b0 b1 cap u hb0pos hb0 hcap
        hcapb1 hhor hpb
      have hI := hinv (clockRoundAt S u) hinc hb1r
      exact fg_noninterference_after_boundary S rho b0 b1 s (clockRoundAt S u + 1) Pn
        hexec hslash hmargin hsleep hscope hno
        (band_step S rho b0 b1 s (clockRoundAt S u) Pn hexec hslash hmargin hsleep hno hI)
        (entry_history_step S rho b0 b1 s (clockRoundAt S u) Pn hexec hslash hmargin
          hsleep hno hI) hheld0 w hw u hb0 (le_of_lt (lt_a_succ_clockRound S u))
    · obtain ⟨rL, hbandL, hentryL, hult⟩ := hanchor u hb0 hcap hhor (not_le.mp hpb)
      exact fg_noninterference_after_boundary S rho b0 b1 s rL Pn hexec hslash hmargin
        hsleep hscope hno hbandL hentryL hheld0 w hw u hb0 (le_of_lt hult)
  refine stableWriteAt_of_sg S rho hexec.core w hw Pn.erase (clockRoundAt S u) ?_ u rfl
    (opening_lt_support_cutoff S u hu0 hcut)
    (le_of_lt (clockRound_lt_opening_succ S u))
    (le_trans (opening_le_clockRound S u hu0) hhor) hsg hL4.2.2 (Or.inr hL4.2.1)
  exact Nat.lt_of_lt_of_le (Nat.succ_pos s) (succ_le_clockRound S s b0 u hmargin hb0)

#print axioms stableWriteCoverage_of_invariant

/-! ## 3. The composed window statement -/






#print axioms activeG2_mem_filtered_tree
#print axioms stableUserOutputs_of_entryPrefixOutputs





end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
