module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.StableCoverageAssembly
public import DecoupledConsensusProofs.Execution.OutputSeedCore
public import DecoupledConsensusProofs.Protocol.Handlers.StableOutputSeed
public import DecoupledConsensusProofs.Protocol.Grades.AwakeParticipation

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Corrected confirmation-coverage consumer

Additive twins of the outage consumer use `HonestConfirmedAbove'`. Clause 3
is retained in the input fold for the proof-layer audit, but the consumer does
not project it: round support uses clauses 1 and 2, and all output assembly
uses clause 5.
-/

namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Internal.NamedOutageEntry Internal.NamedStableChainOutage Internal.NamedJointOutage
open Internal.NamedOutageEntry.History
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

local instance (S : Setup V) (rho : NamedRun V) (P : NamedBlock V)
    (r : Round) (v : V) : Decidable (NeedsSG S rho P r v) :=
  inferInstanceAs (Decidable (¬ Block.Preceq P.erase
    (NamedRun.readAt S rho (domain S.E S.hc r .g1) v).st.core.F))

/-- Clause packing with the corrected coverage predicate. -/
theorem honestConfirmedAbove_of_base_clauses'
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s : Round) (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hseed : OutputSeed S rho b0 s P)
    (hbudget : StableRetentionBudget S rho v s P b1)
    (hno : NoHonestConflictAbove S rho b0 P)
    (h1 : HonestConfirmedAtOrAbove S rho b0 s P) :
    HonestConfirmedAbove' S rho b0 s P := by
  have h2 : HonestHeadHeldAbove S rho b0 s P :=
    stage2_honestHeadHeldAbove S rho b0 b1 s P hexec h1
  obtain ⟨Pn, hPe, _, _⟩ :=
    NamedBoundaryHolding.stable_prefix_held_at_boundary
      S rho b0 b1 hexec hsleep v hv s P hmargin hseed hno
  have hseedPn : OutputSeed S rho b0 s Pn.erase := by simpa only [hPe] using hseed
  have hnoPn : NoHonestConflictAbove S rho b0 Pn.erase := by simpa only [hPe] using hno
  have h1Pn : HonestConfirmedAtOrAbove S rho b0 s Pn.erase := by
    simpa only [hPe] using h1
  have h2Pn : HonestHeadHeldAbove S rho b0 s Pn.erase := by
    simpa only [hPe] using h2
  have hbudgetPn : StableRetentionBudget S rho v s Pn.erase b1 := by
    simpa only [hPe] using hbudget
  have h5Pn := stage2_preBoundaryFrames S rho b0 b1 v s Pn hexec hslash
    hsleep hforming hv hmargin hseedPn hnoPn h1Pn h2Pn hbudgetPn
  have h5 : PreBoundaryFrames S rho b0 s P := by simpa only [hPe] using h5Pn
  exact ⟨h1, h2, h5⟩

/-- Round-invariant base with the corrected four-clause fold. -/
theorem roundInvariant_base'
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hsleep : OutageSleepyThroughout S rho) (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hseed : OutputSeed S rho b0 s Pn.erase)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hconf : HonestConfirmedAbove' S rho b0 s Pn.erase)
    (hbudget : StableRetentionBudget S rho v s Pn.erase b1)
    (hheld0 : ∀ w ∈ rho.honest, Pn ∈
      (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hr : DomainIncluded S rho b0 r)
    (hrb1 : domain S.E S.hc r .g2 ≤ b1 + S.E.Δ)
    (hfirst : S.a (r - 1) < b0)
    (hentry : IntrinsicHighEntryHistory S rho Pn r) :
    RoundInvariant S rho b0 Pn r where
  included := hr
  prefix_scope := hscope
  entry_history := hentry
  conflicting_band :=
    NamedConflictingCarrierBand.intrinsic_conflicting_carrier_band
      S rho b0 b1 s r Pn hexec hmargin hsleep hentry
  source_history := NamedCheckpointRows.signed_source_history S rho r
  old_rows := fun _hhor w _hw _B hB =>
    NamedCheckpointRows.prior_carrier_rows_at_checkpoint
      S rho hexec.core.toNamedScheduleWellFormed hexec.core.toNamedUnforgeable w r hB
  fg := fun _hhor w hw =>
    let h := fg_noninterference_after_boundary S rho b0 b1 s r Pn
      hexec hslash hmargin hsleep hscope hno
      (NamedConflictingCarrierBand.intrinsic_conflicting_carrier_band
        S rho b0 b1 s r Pn hexec hmargin hsleep hentry)
      hentry hheld0 w hw (S.a r) hr.2.1 le_rfl
    ⟨h.2.1, h.2.2⟩
  common_support :=
    common_support_base_at S rho b0 b1 v s r Pn hexec hsleep hforming hv
      hmargin hseed hscope hno hconf.1 hconf.2.1 hbudget hentry hr.1
      (by
        by_contra hcon
        have hm : S.a (s + 1) + S.E.Δ ≤ b0 := hmargin
        have hbad : S.a (s + 1) + S.E.Δ ≤ S.a (s + 1) :=
          (hm.trans hr.2.1).trans (Assembly.a_mono S (Nat.not_lt.mp hcon))
        exact absurd hbad (not_le.mpr (lt_add_of_pos_right _ S.E.Δ_pos)))
      hrb1 hfirst
  sg :=
    sg_at_domain_read_of_common_support S rho b0 b1 s r Pn hexec hslash hsleep
      hforming hscope hr hmargin hno
      (NamedConflictingCarrierBand.intrinsic_conflicting_carrier_band
        S rho b0 b1 s r Pn hexec hmargin hsleep hentry)
      hentry hheld0 (base_hpost S rho b0 r Pn hfirst)
      ⟨hconf.1, hconf.2.1⟩ v hv hseed
      (common_support_base_at S rho b0 b1 v s r Pn hexec hsleep hforming hv
      hmargin hseed hscope hno hconf.1 hconf.2.1 hbudget hentry hr.1
        (by
          by_contra hcon
          have hm : S.a (s + 1) + S.E.Δ ≤ b0 := hmargin
          have hbad : S.a (s + 1) + S.E.Δ ≤ S.a (s + 1) :=
            (hm.trans hr.2.1).trans (Assembly.a_mono S (Nat.not_lt.mp hcon))
          exact absurd hbad (not_le.mpr (lt_add_of_pos_right _ S.E.Δ_pos)))
        hrb1 hfirst)

/-- Round-invariant successor with the corrected fold. -/
theorem roundInvariant_step'
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hsleep : OutageSleepyThroughout S rho) (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hseed : OutputSeed S rho b0 s Pn.erase)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hconf : HonestConfirmedAbove' S rho b0 s Pn.erase)
    (hbudget : StableRetentionBudget S rho v s Pn.erase b1)
    (hheld0 : ∀ w ∈ rho.honest, Pn ∈
      (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hall : ∀ q : Round, RoundIncluded S rho b0 q → q ≤ r →
      RoundInvariant S rho b0 Pn q)
    (hinv : RoundInvariant S rho b0 Pn r)
    (hnext : DomainIncluded S rho b0 (r + 1))
    (hrb1 : domain S.E S.hc (r + 1) .g2 ≤ b1 + S.E.Δ) :
    RoundInvariant S rho b0 Pn (r + 1) := by
  have hstable : OutputSeed S rho b0 s Pn.erase := hseed
  have hpost := honest_confirmed_above_of_invariant
    S rho b0 b1 s Pn (r + 1) hexec hmargin
      (fun q hq hlt => hall q hq (Nat.lt_succ_iff.mp hlt))
  have hband := band_step S rho b0 b1 s r Pn hexec hslash hmargin hsleep hno hinv
  have hentry := entry_history_step S rho b0 b1 s r Pn
    hexec hslash hmargin hsleep hno hinv
  have hsupport := common_support_step S rho b0 b1 v s r Pn
    hexec hforming hv hmargin hsleep hno hentry hbudget hconf.1 hconf.2.1
      (healthySGArrival_of_exec S rho b0 b1 hexec) hinv hnext hrb1 hpost
  have hsg := sg_at_domain_read_of_common_support S rho b0 b1 s (r + 1) Pn
    hexec hslash hsleep hforming hinv.prefix_scope hnext hmargin hno hband hentry
      hheld0 hpost ⟨hconf.1, hconf.2.1⟩ v hv hstable hsupport
  exact roundInvariant_step_of_support S rho b0 b1 s r Pn
    hexec hslash hmargin hsleep hno hheld0 hinv hnext hsupport hsg

private theorem coverage_ind_domain_g1_mono (S : Setup V) {q r : Round}
    (h : q ≤ r) : domain S.E S.hc q .g1 ≤ domain S.E S.hc r .g1 := by
  rw [base_domain_g1_eq_opening, base_domain_g1_eq_opening]
  exact base_opening_mono S h

private theorem coverage_ind_domainIncluded_of_between
    (S : Setup V) (rho : NamedRun V) (b0 : Time) {r0 q p : Round}
    (hr0 : DomainIncluded S rho b0 r0) (hle : r0 ≤ q) (hqp : q ≤ p)
    (hp : DomainIncluded S rho b0 p) : DomainIncluded S rho b0 q :=
  ⟨lt_of_lt_of_le hr0.1 hle, hr0.2.1.trans (Assembly.a_mono S hle),
    (coverage_ind_domain_g1_mono S hqp).trans hp.2.2⟩

private theorem coverage_ind_eq_succ : ∀ a b : Nat,
    a ≤ b + 1 → ¬ a ≤ b → a = b + 1 := by
  intro a b h1 h2
  omega

private theorem coverage_ind_le_zero : ∀ a b : Nat, a ≤ b + 0 → a ≤ b := by
  intro a b h
  omega

/-- All included round invariants with the corrected fold. -/
theorem roundInvariant_all_included'
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s r0 : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hsleep : OutageSleepyThroughout S rho) (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hseed : OutputSeed S rho b0 s Pn.erase)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hconf : HonestConfirmedAbove' S rho b0 s Pn.erase)
    (hbudget : StableRetentionBudget S rho v s Pn.erase b1)
    (hheld0 : ∀ w ∈ rho.honest, Pn ∈
      (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hr0 : DomainIncluded S rho b0 r0) (hfirst : S.a (r0 - 1) < b0)
    (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r0 ≤ q)
    (hentry0 : IntrinsicHighEntryHistory S rho Pn r0) :
    ∀ r : Round, DomainIncluded S rho b0 r →
      domain S.E S.hc r .g2 ≤ b1 + S.E.Δ → RoundInvariant S rho b0 Pn r := by
  have hstable : OutputSeed S rho b0 s Pn.erase := hseed
  have hconv : ∀ q : Round, RoundIncluded S rho b0 q →
      DomainIncluded S rho b0 q := by
    intro q hq
    exact ⟨hq.1, hq.2.1, (FrameForward.domain_le_a S q .g1).trans hq.2.2⟩
  have aux : ∀ k : Nat, domain S.E S.hc (r0 + k) .g2 ≤ b1 + S.E.Δ →
      ∀ q : Round, DomainIncluded S rho b0 q → q ≤ r0 + k →
        RoundInvariant S rho b0 Pn q := by
    intro k
    induction k with
    | zero =>
      intro hb q hq hle
      have hq0 : q = r0 := Nat.le_antisymm
        (coverage_ind_le_zero q r0 hle) (hmin q hq.1 hq.2.1)
      subst hq0
      exact roundInvariant_base' S rho b0 b1 v s q Pn hexec hslash hsleep
        hforming hv hmargin hstable hscope hno hconf hbudget hheld0 hq
        (by simpa using hb) hfirst hentry0
    | succ k ih =>
      intro hb q hq hle
      have hb' : domain S.E S.hc (r0 + k + 1) .g2 ≤ b1 + S.E.Δ := hb
      have hle' : q ≤ r0 + k + 1 := hle
      have hbk : domain S.E S.hc (r0 + k) .g2 ≤ b1 + S.E.Δ :=
        le_trans (base_domain_g2_mono S (Nat.le_succ (r0 + k))) hb'
      by_cases hlt : q ≤ r0 + k
      · exact ih hbk q hq hlt
      · have hqe : q = r0 + k + 1 := coverage_ind_eq_succ q (r0 + k) hle' hlt
        subst hqe
        have hrk : DomainIncluded S rho b0 (r0 + k) :=
          coverage_ind_domainIncluded_of_between S rho b0 hr0
            (Nat.le_add_right r0 k) (Nat.le_succ (r0 + k)) hq
        exact roundInvariant_step' S rho b0 b1 v s (r0 + k) Pn
          hexec hslash hsleep hforming hv hmargin hstable hno hconf hbudget hheld0
          (fun q' hq' hle'' => ih hbk q' (hconv q' hq') hle'')
          (ih hbk (r0 + k) hrk le_rfl) hq hb'
  intro r hr hb
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hmin r hr.1 hr.2.1)
  subst hk
  exact aux k hb (r0 + k) hr le_rfl

#print axioms honestConfirmedAbove_of_base_clauses'
#print axioms roundInvariant_base'
#print axioms roundInvariant_step'
#print axioms roundInvariant_all_included'

/-- `entryPrefixOutputs_upTo_main` with the corrected fold. -/
theorem entryPrefixOutputs_upTo_main'
    (S : Setup V) (rho : NamedRun V) (b0 b1 cap : Time) (v : V)
    (s : Round) (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hsleep : OutageSleepyThroughout S rho) (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hseed : OutputSeed S rho b0 s P) (hno : NoHonestConflictAbove S rho b0 P)
    (hbudget : StableRetentionBudget S rho v s P b1)
    (hconf : HonestConfirmedAbove' S rho b0 s P)
    (hcapb1 : cap ≤ b1 + S.E.Δ) :
    EntryPrefixOutputsUpTo S rho b0 cap P := by
  have hstable : OutputSeed S rho b0 s P := hseed
  obtain ⟨Pn, hPe, hscope, hheld0⟩ :=
    NamedBoundaryHolding.stable_prefix_held_at_boundary
      S rho b0 b1 hexec hsleep v hv s P hmargin hstable hno
  subst hPe
  obtain ⟨r0, hpos, hb, hmin, hfirst, hentry0, _hcase⟩ :=
    NamedFirstCheckpoint.first_checkpoint_history_cases S rho b0 b1 s
      hexec hmargin Pn hscope hno
  have hband0 : IntrinsicConflictingCarrierBand S rho Pn r0 :=
    NamedConflictingCarrierBand.intrinsic_conflicting_carrier_band
      S rho b0 b1 s r0 Pn hexec hmargin hsleep hentry0
  have hanchor : ∀ t : Time, b0 ≤ t → t ≤ cap → t ≤ rho.horizon →
      S.a (clockRoundAt S t) < b0 →
        ∃ r : Round, IntrinsicConflictingCarrierBand S rho Pn r ∧
          IntrinsicHighEntryHistory S rho Pn r ∧ t < S.a r :=
    fun t _ _ _ hstr =>
      ⟨r0, hband0, hentry0, lt_a_of_preBoundary S b0 r0 hb t hstr⟩
  by_cases hshort : domain S.E S.hc r0 .g1 ≤ rho.horizon
  · have hdi0 : DomainIncluded S rho b0 r0 := ⟨hpos, hb, hshort⟩
    have hinv := roundInvariant_all_included' S rho b0 b1 v s r0 Pn
      hexec hslash hsleep hforming hv hmargin hstable hscope hno hconf
        hbudget hheld0 hdi0 hfirst hmin hentry0
    have hcandcov : CandidateReadCoverage S rho b0 cap Pn.erase :=
      candidateReadCoverage_of_invariant S rho b0 b1 cap s Pn
        hexec hslash hmargin hsleep hscope hno hheld0 hinv hconf.2.2
          hcapb1 hanchor
    have hbefore : StableWriteCoverageBefore S rho b0 s Pn.erase :=
      stableWriteCoverageBefore_of_invariant S rho b0 b1 v s Pn
        hexec hmargin hsleep hv hstable hscope hno hinv hconf.2.2
    have hwrite : FormationStableWrite S rho s Pn.erase :=
      formationStableWrite_of_invariant S rho b0 b1 v s Pn
        hexec hmargin hsleep hv hstable hscope hno hinv hconf.2.2
    have hrecord := stable_record_at_boundary_of_coverage
      S rho b0 b1 s Pn.erase hexec hmargin hwrite hbefore
    have hwritecov : StableWriteCoverageWindow S rho b0 cap Pn.erase :=
      stableWriteCoverage_of_invariant S rho b0 b1 cap s Pn
        hexec hslash hmargin hsleep hscope hno hheld0 hinv hconf.2.2
          hcapb1 hanchor
    have hstabcov : ReadStableCoverage S rho b0 cap Pn.erase :=
      readStableCoverage_of_write_coverage S rho b0 cap hexec.core.sorted
        hexec.core.nodup Pn.erase hwritecov hrecord
    exact entryPrefixOutputs_upTo_of_invariant S rho b0 b1 cap s Pn
      hexec hslash hmargin hsleep hscope hno hheld0 hinv hconf.2.2
        hcapb1 hanchor hstabcov hcandcov
  · have hinv : ∀ r : Round, DomainIncluded S rho b0 r →
        domain S.E S.hc r .g2 ≤ b1 + S.E.Δ → RoundInvariant S rho b0 Pn r :=
      fun r hr _ => absurd hr
        (fun h => domainIncluded_false_of_short S rho b0 r0 hmin hshort r h)
    have hcandcov : CandidateReadCoverage S rho b0 cap Pn.erase :=
      candidateReadCoverage_of_invariant S rho b0 b1 cap s Pn
        hexec hslash hmargin hsleep hscope hno hheld0 hinv hconf.2.2
          hcapb1 hanchor
    have hbefore : StableWriteCoverageBefore S rho b0 s Pn.erase :=
      stableWriteCoverageBefore_of_invariant S rho b0 b1 v s Pn
        hexec hmargin hsleep hv hstable hscope hno hinv hconf.2.2
    have hwrite : FormationStableWrite S rho s Pn.erase :=
      formationStableWrite_of_invariant S rho b0 b1 v s Pn
        hexec hmargin hsleep hv hstable hscope hno hinv hconf.2.2
    have hrecord := stable_record_at_boundary_of_coverage
      S rho b0 b1 s Pn.erase hexec hmargin hwrite hbefore
    have hwritecov : StableWriteCoverageWindow S rho b0 cap Pn.erase :=
      stableWriteCoverage_of_invariant S rho b0 b1 cap s Pn
        hexec hslash hmargin hsleep hscope hno hheld0 hinv hconf.2.2
          hcapb1 hanchor
    have hstabcov : ReadStableCoverage S rho b0 cap Pn.erase :=
      readStableCoverage_of_write_coverage S rho b0 cap hexec.core.sorted
        hexec.core.nodup Pn.erase hwritecov hrecord
    exact entryPrefixOutputs_upTo_of_invariant S rho b0 b1 cap s Pn
      hexec hslash hmargin hsleep hscope hno hheld0 hinv hconf.2.2
        hcapb1 hanchor hstabcov hcandcov

/-- Bounded outage outputs with the corrected fold. -/
theorem stable_chain_outage_resilience_from_clauses_main'
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s : Round) (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hsleep : OutageSleepyThroughout S rho) (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hseed : OutputSeed S rho b0 s P) (hno : NoHonestConflictAbove S rho b0 P)
    (hconf : HonestConfirmedAbove' S rho b0 s P)
    (hbudget : StableRetentionBudget S rho v s P b1) :
    StableUserOutputs S rho b0 b1 P := by
  have hstable : OutputSeed S rho b0 s P := hseed
  apply stableUserOutputs_of_entryPrefixOutputs S rho b0 b1 P
  apply entryPrefixOutputs_of_upTo S rho b0 b1 P
  exact entryPrefixOutputs_upTo_main' S rho b0 b1 (b1 + S.E.Δ) v s P
    hexec hslash hsleep hforming hv hmargin hstable hno hbudget hconf le_rfl

#print axioms entryPrefixOutputs_upTo_main'
#print axioms stable_chain_outage_resilience_from_clauses_main'

/-- Cap-straddling seed clauses with the corrected fold. -/
theorem outageCap_seed_clauses'
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hv : v ∈ rho.honest) (hseed : OutputSeed S rho b0 s Pn.erase)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hconf : HonestConfirmedAbove' S rho b0 s Pn.erase)
    (hinv : ∀ q : Round, DomainIncluded S rho b0 q →
      domain S.E S.hc q .g2 ≤ b1 + S.E.Δ → RoundInvariant S rho b0 Pn q)
    (hr : 0 < r)
    (hdomCap : domain S.E S.hc r .g2 ≤ b1 + S.E.Δ)
    (hcapNext : b1 + S.E.Δ < domain S.E S.hc (r + 1) .g2)
    (hopenHor : domain S.E S.hc r .g1 ≤ rho.horizon) :
    IntrinsicHighEntryHistory S rho Pn r ∧
      OutageSGClauseAt S rho Pn.erase r ∧ HonestCarriersAbove S rho Pn.erase r := by
  have hstable : OutputSeed S rho b0 s Pn.erase := hseed
  have hs1 : s + 1 ≤ r := by
    by_contra hnot
    have hrs : r ≤ s := Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hnot)
    have hr1 : r + 1 ≤ s + 1 := Nat.add_le_add_right hrs 1
    have hbad : domain S.E S.hc (r + 1) .g2 ≤ b1 + S.E.Δ :=
      (base_domain_g2_mono S hr1).trans
        ((FrameForward.domain_le_a S (s + 1) .g2).trans
          ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
            (hmargin.trans (hexec.interval.2.1.trans
              (Int.le_add_of_nonneg_right S.E.Δ_pos.le)))))
    exact (not_le_of_gt hcapNext) hbad
  by_cases hpost : b0 ≤ S.a r
  · have hround := hinv r ⟨hr, hpost, hopenHor⟩ hdomCap
    exact ⟨hround.entry_history, hround.sg,
      carriersAbove_of_roundInvariant S rho b0 b1 Pn r hexec hround⟩
  · have hpre : S.a r < b0 := lt_of_not_ge hpost
    have hentry : IntrinsicHighEntryHistory S rho Pn r :=
      Proofs.NamedIntrinsicEntry.initial_intrinsic_history S rho b0 Pn r hscope hno
        ((Assembly.a_mono S (Nat.sub_le r 1)).trans_lt hpre)
    have hsg : OutageSGClauseAt S rho Pn.erase r := by
      intro w hw
      exact hconf.2.2 w hw r hs1 hpre
    have hjoint : S.a r ≤ rho.horizon → ∀ w ∈ rho.honest,
        JointAt S rho Pn r w := by
      intro _ w hw
      have hopen : opening S.E S.hc (s + 1) ≤ S.a r :=
        (base_opening_mono S hs1).trans (incl_opening_le_a S r)
      have hrow := fgRow_before_boundary S rho b0 b1 v s Pn hexec
        hmargin hsleep hv hstable hno w hw (S.a r) hopen hpre.le
      have hcompat := compat_before_boundary S rho b0 b1 s Pn hexec
        hmargin hsleep hscope hno w hw (S.a r) hpre.le
      have hpair := And.intro hrow hcompat
      simpa only [JointAt, checkpoint, roundConfirmationRead,
        Internal.NamedOutageEntry.confirmationReadAt,
        NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock] using hpair
    have hcarriers := carriersAbove_of_sg_clause S rho b0 b1 Pn r
      hexec hr hsg hjoint
    exact ⟨hentry, hsg, hcarriers⟩

/-- First-healthy SG clause with the corrected fold. -/
theorem firstHealthy_sg_clause_of_retention'
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s r0 : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hseed : OutputSeed S rho b0 s Pn.erase)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hconf : HonestConfirmedAbove' S rho b0 s Pn.erase)
    (hbudget : StableRetentionBudget S rho v s Pn.erase b1)
    (hheld0 : ∀ w ∈ rho.honest,
      Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hinv : ∀ r : Round, DomainIncluded S rho b0 r →
      domain S.E S.hc r .g2 ≤ b1 + S.E.Δ → RoundInvariant S rho b0 Pn r)
    (hr0 : 0 < r0)
    (hhealthy : max S.E.t_GST b1 ≤ S.a r0)
    (hpred : S.a (r0 - 1) < max S.E.t_GST b1)
    (hearlyCap : early S.E S.hc r0 .g2 < b1 + S.E.Δ)
    (hopenHor : domain S.E S.hc r0 .g1 ≤ rho.horizon) :
    ∀ w ∈ rho.honest,
      let n := NamedRun.readAt S rho (domain S.E S.hc r0 .g1) w
      Block.Preceq Pn.erase n.st.core.F ∨
        ∃ raw : Block V,
          (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r0).g2 =
            some (some raw) ∧ Block.Preceq Pn.erase raw := by
  have hstable : OutputSeed S rho b0 s Pn.erase := hseed
  have hmax : max S.E.t_GST b1 = b1 := max_eq_right hexec.gst
  have hb1a : b1 ≤ S.a r0 := by simpa only [hmax] using hhealthy
  have hpredb1 : S.a (r0 - 1) < b1 := by simpa only [hmax] using hpred
  have hgap : s + 1 < r0 := by
    by_contra hnot
    have hr0le : r0 ≤ s + 1 := Nat.le_of_not_gt hnot
    have hbad : S.a r0 < S.a (s + 1) + S.E.Δ :=
      (Assembly.a_mono S hr0le).trans_lt (lt_add_of_pos_right _ S.E.Δ_pos)
    have hbound : S.a (s + 1) + S.E.Δ ≤ S.a r0 :=
      hmargin.trans (hexec.interval.2.1.trans hb1a)
    exact (not_lt_of_ge hbound) hbad
  have hslt : s < r0 := Nat.lt_trans (Nat.lt_succ_self s) hgap
  have hnext : DomainIncluded S rho b0 r0 :=
    ⟨hr0, hexec.interval.2.1.trans hb1a, hopenHor⟩
  have hpost : ∀ (a : NamedAttestation V) (t : Time),
      a.val_index ∈ rho.honest → NamedRun.emits S rho a.val_index (.attest a) t →
      b0 ≤ t → a.round < r0 → ∀ key, a.confirmed = some key →
      ∀ K : NamedBlock V, NamedRun.blockInRun S rho K → K.root = key →
      Block.Preceq Pn.erase K.erase := by
    apply honest_confirmed_above_of_invariant S rho b0 b1 s Pn r0 hexec hmargin
    intro q hq hqr
    have hqDom : domain S.E S.hc q .g2 ≤ b1 + S.E.Δ :=
      (FrameForward.domain_le_a S q .g2).trans
        ((Assembly.a_mono S (Nat.le_sub_one_of_lt hqr)).trans
          (hpredb1.le.trans (Int.le_add_of_nonneg_right S.E.Δ_pos.le)))
    exact hinv q ⟨hq.1, hq.2.1,
      (FrameForward.domain_le_a S q .g1).trans hq.2.2⟩ hqDom
  by_cases hpre : S.a (r0 - 1) < b0
  · have hentry : IntrinsicHighEntryHistory S rho Pn r0 :=
      Proofs.NamedIntrinsicEntry.initial_intrinsic_history S rho b0 Pn r0 hscope hno hpre
    have hband : IntrinsicConflictingCarrierBand S rho Pn r0 :=
      NamedConflictingCarrierBand.intrinsic_conflicting_carrier_band
        S rho b0 b1 s r0 Pn hexec hmargin hsleep hentry
    have hsupport := common_support_base_at_of_early S rho b0 b1 v s r0 Pn
      hexec hsleep hforming hv hmargin hstable hscope hno hconf.1 hconf.2.1
        hbudget hentry hr0 hgap hearlyCap hpre
    exact sg_at_domain_read_of_common_support_at S rho b0 b1 s r0 Pn
      hexec hslash hsleep hforming hscope hr0 hslt hopenHor hmargin hno
        hband hentry hheld0 hpost ⟨hconf.1, hconf.2.1⟩ v hv hstable hsupport
  · have hb0pred : b0 ≤ S.a (r0 - 1) := le_of_not_gt hpre
    have honeLt : 1 < r0 := (Nat.succ_le_succ (Nat.zero_le s)).trans_lt hgap
    have hpredPos : 0 < r0 - 1 := Nat.sub_pos_iff_lt.mpr honeLt
    have hpredHor : S.a (r0 - 1) ≤ rho.horizon :=
      hpredb1.le.trans hexec.interval.2.2
    have hprevInc : DomainIncluded S rho b0 (r0 - 1) :=
      ⟨hpredPos, hb0pred,
        (FrameForward.domain_le_a S (r0 - 1) .g1).trans hpredHor⟩
    have hpredDom : domain S.E S.hc (r0 - 1) .g2 ≤ b1 + S.E.Δ :=
      (FrameForward.domain_le_a S (r0 - 1) .g2).trans
        (hpredb1.le.trans (Int.le_add_of_nonneg_right S.E.Δ_pos.le))
    have hprev := hinv (r0 - 1) hprevInc hpredDom
    have hrSucc : r0 - 1 + 1 = r0 :=
      Nat.sub_add_cancel (Nat.succ_le_iff.mpr hr0)
    have hentry : IntrinsicHighEntryHistory S rho Pn r0 := by
      rw [← hrSucc]
      exact entry_history_step S rho b0 b1 s (r0 - 1) Pn
        hexec hslash hmargin hsleep hno hprev
    have hband : IntrinsicConflictingCarrierBand S rho Pn r0 := by
      rw [← hrSucc]
      exact band_step S rho b0 b1 s (r0 - 1) Pn
        hexec hslash hmargin hsleep hno hprev
    have hsupport := common_support_step_of_early S rho b0 b1 v s (r0 - 1) Pn
      hexec hforming hv hmargin hsleep hno (by simpa only [hrSucc] using hentry)
        hbudget hconf.1 hconf.2.1 (healthySGArrival_of_exec S rho b0 b1 hexec)
        hprev (by simpa only [hrSucc] using hnext)
        (by simpa only [hrSucc] using hearlyCap)
        (by simpa only [hrSucc] using hpost)
    exact sg_at_domain_read_of_common_support_at S rho b0 b1 s r0 Pn
      hexec hslash hsleep hforming hscope hr0 hslt hopenHor hmargin hno
        hband hentry hheld0 hpost ⟨hconf.1, hconf.2.1⟩ v hv hstable
        (by simpa only [hrSucc] using hsupport)

#print axioms outageCap_seed_clauses'
#print axioms firstHealthy_sg_clause_of_retention'

/-- Exact read-level viability from the history whose upper round is the read's
own round. This is the tight form needed by the mutual induction. -/
private theorem coverage_mutual_relativeG2_viability
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round)
    (Pn : NamedBlock V) (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hentry : IntrinsicHighEntryHistory S rho Pn r)
    (hheld0 : ∀ w ∈ rho.honest,
      Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hb0 : b0 ≤ domain S.E S.hc r .g2) :
    ∀ w ∈ rho.honest,
      Block.Preceq Pn.erase
          (Protocol.get_fg_root
            (Proofs.HealingSurface.relativeG2Read S rho r w).st.core.toHealing.toFG) ∨
        Pn.erase ∈ Internal.PhaseGrades.filteredTree
          (Proofs.HealingSurface.relativeG2Read S rho r w) := by
  intro w hw
  have h := fgRootAbove_or_filtered_at_stateBeforeTime_of_entry
    S rho b0 b1 s r Pn hexec hslash hmargin hsleep hscope hno hentry
      hheld0 w hw (domain S.E S.hc r .g2) hb0
      (FrameForward.domain_le_a S r .g2)
  simpa only [Proofs.HealingSurface.relativeG2Read,
    Internal.PhaseGrades.filteredTree] using h

/-- Exact confirmation-read compatibility before the action of the history's
upper round. -/
private theorem coverage_mutual_fg_compatibility
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round)
    (Pn : NamedBlock V) (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hentry : IntrinsicHighEntryHistory S rho Pn r)
    (hheld0 : ∀ w ∈ rho.honest,
      Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (w : V) (hw : w ∈ rho.honest) (u : Time)
    (hb0 : b0 ≤ u) (hu : u < S.a r) :
    Block.compatible Pn.erase
      (Protocol.get_fg_root
        (NamedActionReads.confirmationReadAt S rho w u).st.core.toHealing.toFG) = true := by
  have h := fg_compatible_at_read_of_entry S rho b0 b1 s r Pn hexec
    hslash hmargin hsleep hscope hno hentry hheld0 w hw u hb0 hu
  simpa only [NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using h

/-- Carry the stable floor from one G2 domain to the next. This is the
pointwise form of `stable_above_P_through_succ_of_floor`; its premise is only
the start value that the proof consumes. -/
private theorem coverage_mutual_stable_at_next_g2
    (S : Setup V) (rho : NamedRun V) (P : Block V) (r : Round)
    (core : NamedAdmissibleCore S rho)
    (hstart : ∀ w ∈ rho.honest, Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core))
    (hviable : ∀ u ∈ rho.honest,
      Block.Preceq P
          (Protocol.get_fg_root
            (Proofs.HealingSurface.relativeG2Read S rho (r + 2) u).st.core.toHealing.toFG) ∨
        P ∈ Internal.PhaseGrades.filteredTree
          (Proofs.HealingSurface.relativeG2Read S rho (r + 2) u))
    (hwrite : ∀ w ∈ rho.honest, ∀ (k : Nat) (u : Time),
      domain S.E S.hc (r + 1) .g2 ≤ u →
      u < domain S.E S.hc (r + 2) .g2 →
      rho.events[k]? = some (.tick w u) →
      0 < S.E.slotOf u →
      u = Protocol.support_cutoff S.E (S.E.slotOf u) →
      ∀ G, dutyStableRoot S
          (NamedActionReads.confirmationReadFrom
            S (NamedRun.stateBefore S rho k w) u) = some G →
        Block.Preceq P (NamedRun.stateBefore S rho k w).st.core.latest_stable →
        Block.Preceq P G ∨ Block.Preceq G P) :
    ∀ w ∈ rho.honest, Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 2) .g2) w).st.core) := by
  intro w hw
  let start := domain S.E S.hc (r + 1) .g2
  let stop := domain S.E S.hc (r + 2) .g2
  let i := (rho.events.filter (fun e => decide (e.time < start))).length
  let j := (rho.events.filter (fun e => decide (e.time < stop))).length
  have hstartStop : start ≤ stop := base_domain_g2_mono S (Nat.le_succ (r + 1))
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
  have hhold : Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho start w).st.core) :=
    hstart w hw
  have hcases := stateBefore_stable_covered_of_comparable S rho w i j hij
    (by
      rw [← hi]
      unfold Protocol.get_stable at hhold
      split at hhold
      · exact Or.inr hhold
      · exact Or.inl hhold)
    (fun k u hik hkj he hpos hcut G hG hlat => by
      have huStart : start ≤ u := Proofs.Optimistic.le_time_of_index_ge S
        core.toNamedScheduleWellFormed (t := start) (j := k) hik he
      have huStop : u < stop := by
        have hins := Proofs.Optimistic.filter_true_of_index_lt S
          core.toNamedScheduleWellFormed (fun e => decide (e.time < stop))
          (Proofs.Optimistic.downward_lt stop) hkj he
        simpa only [decide_eq_true_eq, NamedEvent.time] using hins
      exact hwrite w hw k u (by simpa only [start] using huStart)
        (by simpa only [stop] using huStop) he hpos hcut G hG hlat)
  have hcompat : Block.compatible P
      (NamedRun.stateBeforeTime S rho stop w).st.core.F = true := by
    rcases hviable w hw with hroot | htree
    · have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        S rho stop w
      have hFroot := Proofs.Records.preceq_get_fg_root_of_F
        (st := (NamedRun.stateBeforeTime S rho stop w).st.core.toHealing.toFG)
        (by simpa only [Protocol.Store.toHealing] using hFJ)
      have hroot' : Block.Preceq P
          (Protocol.get_fg_root
            (NamedRun.stateBeforeTime S rho stop w).st.core.toHealing.toFG) := by
        simpa only [stop, Proofs.HealingSurface.relativeG2Read,
          Internal.PhaseGrades.filteredTree] using hroot
      exact Block.compatible_of_preceq_common hroot' hFroot
    · have hFleP := q10_filtered_F (by
          simpa only [stop, Proofs.HealingSurface.relativeG2Read,
            Internal.PhaseGrades.filteredTree] using htree)
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr hFleP
  rw [hj]
  rw [hj] at hcompat
  rcases hcases with hF | hstable
  · have hFstable : Block.Preceq
        (NamedRun.stateBefore S rho j w).st.core.F
        (Protocol.get_stable (NamedRun.stateBefore S rho j w).st.core) := by
      unfold Protocol.get_stable
      split
      · assumption
      · exact Block.preceq_self _
    exact Block.preceq_trans hF hFstable
  · exact preceq_get_stable_of_cases _ (Or.inr hstable) hcompat

/--  clauses-form outage persistence. -/
theorem stable_chain_outage_resilience_of_clauses''
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s : Round) (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hseed : OutputSeed S rho b0 s P)
    (hbudget : StableRetentionBudget S rho v s P b1)
    (hno : NoHonestConflictAbove S rho b0 P)
    (hconf : HonestConfirmedAbove' S rho b0 s P) :
    StableUserOutputsFrom S rho b0 P := by
  have hstable : OutputSeed S rho b0 s P := hseed
  obtain ⟨Pn, hPe, hscope, hheld0⟩ :=
    NamedBoundaryHolding.stable_prefix_held_at_boundary
      S rho b0 b1 hexec hsleep v hv s P hmargin hstable hno
  subst hPe
  obtain ⟨rB, hBpos, hBact, hBmin, hBfirst, hBentry, _hBcase⟩ :=
    NamedFirstCheckpoint.first_checkpoint_history_cases S rho b0 b1 s hexec hmargin Pn
      hscope hno
  have hinv : ∀ q : Round, DomainIncluded S rho b0 q →
      domain S.E S.hc q .g2 ≤ b1 + S.E.Δ →
      RoundInvariant S rho b0 Pn q := by
    by_cases hshort : domain S.E S.hc rB .g1 ≤ rho.horizon
    · have hdiB : DomainIncluded S rho b0 rB := ⟨hBpos, hBact, hshort⟩
      exact roundInvariant_all_included' S rho b0 b1 v s rB Pn hexec hslash hsleep
        hforming hv hmargin hstable hscope hno hconf hbudget hheld0 hdiB hBfirst hBmin
        hBentry
    · intro q hq _
      exact absurd hq
        (domainIncluded_false_of_short S rho b0 rB hBmin hshort q)
  have hout : StableUserOutputs S rho b0 b1 Pn.erase :=
    stable_chain_outage_resilience_from_clauses_main' S rho b0 b1 v s Pn.erase
      hexec hslash hsleep hforming hv hmargin hstable hno hconf hbudget
  obtain ⟨r0, hr0, hhealthy, hminHealthy, hpredHealthy⟩ :=
    firstHealthyAction_exists S rho b0 b1 s hexec hmargin
  have hmax : max S.E.t_GST b1 = b1 := max_eq_right hexec.gst
  have hpost0 : b1 ≤ S.a r0 := by
    simpa only [hmax] using hhealthy
  have hpredB1 : S.a (r0 - 1) < b1 := by
    simpa only [hmax] using hpredHealthy
  have hprevSucc : r0 - 1 + 1 = r0 :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hr0)
  have hb0cap : b0 ≤ b1 + S.E.Δ :=
    hexec.interval.2.1.trans (Int.le_add_of_nonneg_right S.E.Δ_pos.le)
  have hgap : s + 1 < r0 := by
    by_contra hnot
    have hr0le : r0 ≤ s + 1 := Nat.le_of_not_gt hnot
    have hbad : S.a r0 < S.a (s + 1) + S.E.Δ :=
      (Assembly.a_mono S hr0le).trans_lt
        (lt_add_of_pos_right _ S.E.Δ_pos)
    have hbound : S.a (s + 1) + S.E.Δ ≤ S.a r0 :=
      hmargin.trans (hexec.interval.2.1.trans hpost0)
    exact (not_lt_of_ge hbound) hbad
  have hsgsBefore : TransitionSGClauses S rho b0 Pn (r0 - 1) := by
    intro q hq hqle w hw
    have hqact : S.a q < b1 :=
      (Assembly.a_mono S hqle).trans_lt hpredB1
    have hqcap : domain S.E S.hc q .g2 ≤ b1 + S.E.Δ :=
      (FrameForward.domain_le_a S q .g2).trans
        (hqact.le.trans (Int.le_add_of_nonneg_right S.E.Δ_pos.le))
    exact (hinv q hq hqcap).sg w hw
  have ha0 : S.a 0 < b0 := by
    have hzero : S.a 0 ≤ S.a (s + 1) := Assembly.a_mono S (Nat.zero_le _)
    exact hzero.trans_lt (lt_of_lt_of_le (lt_add_of_pos_right _ S.E.Δ_pos) hmargin)
  have hentryBefore : ∀ q : Round, 0 < q → q ≤ r0 →
      IntrinsicHighEntryHistory S rho Pn q := by
    intro q hq hqle
    by_cases hbefore : S.a (q - 1) < b0
    · exact Proofs.NamedIntrinsicEntry.initial_intrinsic_history S rho b0 Pn q hscope hno
        hbefore
    · have hqpred : 0 < q - 1 := by
        by_contra hnot
        have hqsub : q - 1 = 0 := Nat.eq_zero_of_not_pos hnot
        have hqle1 : q ≤ 1 := Nat.sub_eq_zero_iff_le.mp hqsub
        have hqone : q = 1 := Nat.le_antisymm hqle1
          (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq))
        subst q
        have hbefore0 : ¬ S.a 0 < b0 := by simpa using hbefore
        exact (not_le_of_gt ha0) (not_lt.mp hbefore0)
      have hpredle : q - 1 ≤ r0 - 1 := Nat.sub_le_sub_right hqle 1
      have hpredAction : S.a (q - 1) ≤ S.a (r0 - 1) :=
        Assembly.a_mono S hpredle
      have hpredHor : S.a (q - 1) ≤ rho.horizon :=
        hpredAction.trans (hpredB1.le.trans hexec.interval.2.2)
      have hinc : DomainIncluded S rho b0 (q - 1) :=
        ⟨hqpred, le_of_not_gt hbefore,
          (FrameForward.domain_le_a S (q - 1) .g1).trans hpredHor⟩
      have hcap : domain S.E S.hc (q - 1) .g2 ≤ b1 + S.E.Δ :=
        (FrameForward.domain_le_a S (q - 1) .g2).trans
          (hpredAction.trans
            (hpredB1.le.trans (Int.le_add_of_nonneg_right S.E.Δ_pos.le)))
      have hp := hinv (q - 1) hinc hcap
      have hcar := carriersAbove_of_roundInvariant S rho b0 b1 Pn (q - 1) hexec hp
      have hsucc : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hq)
      simpa only [hsucc] using
        (entry_history_succ_of_carrierAbove S rho b0 b1 (q - 1) Pn hexec
          hscope hqpred hp.entry_history hcar)
  by_cases hopen0 : domain S.E S.hc r0 (Phase.g1) ≤ rho.horizon
  · have hdom0Hor : domain S.E S.hc r0 .g2 ≤ rho.horizon :=
      (q10_domain_g2_lt_domain_g1 S r0).le.trans hopen0
    have hcapStr := outageCap_g2_straddle_exists S b0 b1 s
      hexec.interval.2.1 hmargin
    obtain ⟨rc, hrcpos, hrcCap, hcapNext⟩ := hcapStr
    have hearlyStrict : early S.E S.hc (r0 + 1) .g2 <
        domain S.E S.hc (r0 + 1) .g2 := by
      unfold early domain
      simp only [Phase.earlyOffset, Phase.domainOffset]
      nlinarith [S.E.Δ_pos]
    have hcapEarlyNext : b1 + S.E.Δ ≤ early S.E S.hc (r0 + 1) .g2 :=
      (Int.add_le_add_right hpost0 S.E.Δ).trans
        (healthyAction_add_delta_le_next_earlyG2 S r0)
    have hdomNextCap : b1 + S.E.Δ <
        domain S.E S.hc (r0 + 1) .g2 := hcapEarlyNext.trans_lt hearlyStrict
    have hrcUpper : rc ≤ r0 := by
      by_contra hnot
      have hle : r0 + 1 ≤ rc := Nat.succ_le_of_lt (Nat.lt_of_not_ge hnot)
      exact (not_lt_of_ge hrcCap)
        (hdomNextCap.trans_le (base_domain_g2_mono S hle))
    have hrcLower : r0 - 1 ≤ rc := by
      by_contra hnot
      have hle : rc + 1 ≤ r0 - 1 := Nat.succ_le_of_lt (Nat.lt_of_not_ge hnot)
      have hprevCap : domain S.E S.hc (r0 - 1) .g2 ≤ b1 + S.E.Δ :=
        (FrameForward.domain_le_a S (r0 - 1) .g2).trans
          (hpredB1.le.trans (Int.le_add_of_nonneg_right S.E.Δ_pos.le))
      exact (not_lt_of_ge hprevCap)
        (hcapNext.trans_le (base_domain_g2_mono S hle))
    have hrcCases : rc = r0 - 1 ∨ rc = r0 := by
      by_cases heq : rc = r0
      · exact Or.inr heq
      · left
        have hlt : rc < r0 := lt_of_le_of_ne hrcUpper heq
        exact Nat.le_antisymm (Nat.le_pred_of_lt hlt) hrcLower
    have finish : OutageMutualStateAt S rho Pn b0 s r0 →
        StableUserOutputsFrom S rho b0 Pn.erase := by
      intro hstate
      have hgst0 : S.E.t_GST ≤ S.a r0 := hexec.gst.trans hpost0
      have hb0next0 : b0 ≤ domain S.E S.hc (r0 + 1) .g2 :=
        hb0cap.trans hdomNextCap.le
      have hinvAll := outageInvariant_all S rho b0 b1 s r0 Pn hexec hslash hmargin
        hsleep hforming hscope hno hheld0 hstate hgst0 hb0next0
      have hentryAll : ∀ q : Round, 0 < q → IntrinsicHighEntryHistory S rho Pn q := by
        intro q hq
        by_cases hle : q ≤ r0
        · exact hentryBefore q hq hle
        · have hqpred : r0 ≤ q - 1 :=
            Nat.le_pred_of_lt (Nat.lt_of_not_ge hle)
          have hI := hinvAll (q - 1) hqpred
          have hsucc : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hq)
          simpa only [hsucc] using hI.2
      have hK6all : ∀ t, b0 ≤ t → t ≤ rho.horizon → ∀ w ∈ rho.honest,
          Block.Preceq Pn.erase
              (Protocol.get_fg_root
                (NamedRun.readAt S rho t w).st.core.toHealing.toFG) ∨
            Pn.erase ∈ Internal.PhaseGrades.filteredTree (NamedRun.readAt S rho t w) := by
        intro t ht0 hth w hw
        let q := clockRoundAt S t + 1
        have hq : 0 < q := Nat.succ_pos _
        have hqt : t < S.a q :=
          (clockRound_lt_opening_succ S t).trans_le (incl_opening_le_a S q)
        exact fgRootAbove_or_filtered_at_read_of_entry S rho b0 b1 s q Pn hexec
          hslash hmargin hsleep hscope hno (hentryAll q hq) hheld0 w hw t ht0 hqt
      have hsgs0 : TransitionSGClauses S rho b0 Pn r0 := by
        intro q hq hqle w hw
        by_cases hqprev : q ≤ r0 - 1
        · exact hsgsBefore q hq hqprev w hw
        · have hqeq : q = r0 := by
            have hle' : q ≤ (r0 - 1) + 1 := by
              simpa only [hprevSucc] using hqle
            have hge : r0 ≤ q := by
              simpa only [Nat.succ_eq_add_one, hprevSucc] using
                (Nat.succ_le_of_lt (Nat.lt_of_not_ge hqprev))
            exact Nat.le_antisymm (by simpa only [hprevSucc] using hle') hge
          have hs := hstate.2.2 w hw
          simpa [hqeq] using hs
      have htransition0 := stableUserOutputs_transition_of_sg S rho b0 b1 s r0 Pn
        hexec.core hexec.interval.2.1 hmargin hsgs0 hconf.2.2 hout hK6all
      by_cases hopen1 : domain S.E S.hc (r0 + 1) .g1 ≤ rho.horizon
      · have hdom1Hor : domain S.E S.hc (r0 + 1) .g2 ≤ rho.horizon :=
          (q10_domain_g2_lt_domain_g1 S (r0 + 1)).le.trans hopen1
        have hb0open1 : b0 ≤ domain S.E S.hc (r0 + 1) .g1 :=
          hb0next0.trans (q10_domain_g2_lt_domain_g1 S (r0 + 1)).le
        have hK6opening1 : ∀ w ∈ rho.honest,
            Block.Preceq Pn.erase
                (Protocol.get_fg_root
                  (NamedRun.readAt S rho
                    (domain S.E S.hc (r0 + 1) .g1) w).st.core.toHealing.toFG) ∨
              Pn.erase ∈ Internal.PhaseGrades.filteredTree
                (NamedRun.readAt S rho (domain S.E S.hc (r0 + 1) .g1) w) := by
          intro w hw
          exact fgRootAbove_or_filtered_at_read_of_entry S rho b0 b1 s (r0 + 1) Pn
            hexec hslash hmargin hsleep hscope hno
            (hentryAll (r0 + 1) (Nat.succ_pos r0)) hheld0 w hw
            (domain S.E S.hc (r0 + 1) .g1) hb0open1
            (q10_domain_lt_a S (r0 + 1) .g1)
        have hsg1 := opening_sg_clause_of_outageInvariant S rho b0 b1 s r0 Pn hexec
          hslash hmargin hsleep hforming hscope hno hheld0 hstate.1 hgst0
          hstate.2.1 hb0open1 hopen1
        have hjoint1 : S.a (r0 + 1) ≤ rho.horizon → ∀ w ∈ rho.honest,
            Internal.NamedJointOutage.JointAt S rho Pn (r0 + 1) w := by
          intro hact w hw
          exact jointAt_of_entry_history S rho b0 b1 s (r0 + 1) Pn hexec
            hslash hmargin hsleep hscope hno
            (hentryAll (r0 + 1) (Nat.succ_pos r0)) hheld0
            (hb0next0.trans
              ((q10_domain_g2_lt_domain_g1 S (r0 + 1)).le.trans
                (q10_domain_lt_a S (r0 + 1) .g1).le)) hact w hw
        have hcar1 : HonestCarriersAbove S rho Pn.erase (r0 + 1) :=
          carriersAbove_of_sg_clause S rho b0 b1 Pn (r0 + 1) hexec
            (Nat.succ_pos r0) hsg1 hjoint1
        have hsgs1 : TransitionSGClauses S rho b0 Pn (r0 + 1) := by
          intro q hq hqle w hw
          by_cases hq0 : q ≤ r0
          · exact hsgs0 q hq hq0 w hw
          · have hqeq : q = r0 + 1 := by
              exact Nat.le_antisymm hqle
                (Nat.succ_le_of_lt (Nat.lt_of_not_ge hq0))
            subst q
            exact hsg1 w hw
        have htransition1 := stableUserOutputs_transition_of_sg S rho b0 b1 s (r0 + 1)
          Pn hexec.core hexec.interval.2.1 hmargin hsgs1 hconf.2.2 hout hK6all
        by_cases hopen2 : domain S.E S.hc (r0 + 2) .g1 ≤ rho.horizon
        · have hdom2Hor : domain S.E S.hc (r0 + 2) .g2 ≤ rho.horizon :=
            (q10_domain_g2_lt_domain_g1 S (r0 + 2)).le.trans hopen2
          have hb0seed : b0 < domain S.E S.hc (r0 + 1) .g2 :=
            hb0cap.trans_lt hdomNextCap
          have hseed : PostOutageSeedAt S rho Pn.erase (r0 + 1) :=
            postOutageSeedAt_of_sg_clause S rho b0 b1 Pn (r0 + 1) hexec
              (Nat.succ_pos r0) hsg1 hcar1 hstate.2.1 hK6all hb0seed hdom2Hor
          have hK6 : ∀ q, r0 + 1 ≤ q → ∀ u ∈ rho.honest,
              Block.Preceq Pn.erase
                  (Protocol.get_fg_root
                    (NamedActionReads.actionReadAt S rho u q).st.core.toHealing.toFG) ∨
                Pn.erase ∈ Protocol.get_filtered_block_tree
                  (NamedActionReads.actionReadAt S rho u q).st.core.toHealing.toFG := by
            intro q hq w hw
            have hentryQ := hentryAll q (Nat.lt_of_lt_of_le (Nat.succ_pos r0) hq)
            have hb0q : b0 ≤ S.a q := by
              exact hb0next0.trans
                ((base_domain_g2_mono S hq).trans
                  (FrameForward.domain_le_a S q .g2))
            have hband := NamedConflictingCarrierBand.intrinsic_conflicting_carrier_band
              S rho b0 b1 s q Pn hexec hmargin hsleep hentryQ
            have hh := fg_noninterference_after_boundary S rho b0 b1 s q Pn hexec
              hslash hmargin hsleep hscope hno hband hentryQ hheld0 w hw
              (S.a q) hb0q le_rfl
            simpa only [NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
              NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
              Protocol.NamedStore.setClock, Protocol.NamedDuties.update_confirmation_with]
              using hh.2.1
          have hfg : ∀ q, r0 + 1 ≤ q → ∀ w ∈ rho.honest, ∀ u,
              domain S.E S.hc (q + 1) .g2 ≤ u →
              u < domain S.E S.hc (q + 2) .g2 →
              u = Protocol.support_cutoff S.E (S.E.slotOf u) →
              Block.compatible Pn.erase
                (Protocol.get_fg_root
                  (NamedActionReads.confirmationReadAt S rho w u).st.core.toHealing.toFG) =
                true := by
            intro q hq w hw u hlo hhi hcut
            have hb0u : b0 ≤ u := by
              exact hb0next0.trans
                ((base_domain_g2_mono S (hq.trans (Nat.le_succ q))).trans hlo)
            exact fg_compatible_at_confirmation_read_of_entry S rho b0 b1 s q Pn hexec
              hslash hmargin hsleep hscope hno
              (hentryAll (q + 2) (Nat.succ_pos _)) hheld0 w hw u hhi hb0u
          have hpost : ∀ q, r0 + 1 < q → 0 < q →
              domain S.E S.hc q .g1 ≤ rho.horizon →
              PostOutageAboveTruncated S rho Pn.erase q := by
            intro q hq _ hqHor
            exact postOutageAboveTruncated_after_transition S rho b0 b1 Pn.erase (r0 + 1)
              hexec hforming hseed hK6 hK6all hfg
                (hpost0.trans (Assembly.a_mono S (Nat.le_succ r0))) q hq hqHor
          exact stableUserOutputsFrom_of_induction S rho b0 b1 s (r0 + 1) Pn.erase
            hexec.core hexec.interval.2.1 hmargin hout htransition1 hpost hK6all
        · have hpost1 : ∀ q, r0 + 1 < q → 0 < q →
              domain S.E S.hc q .g1 ≤ rho.horizon →
              PostOutageAboveTruncated S rho Pn.erase q := by
            intro q hq _ hqHor
            have hqge : r0 + 2 ≤ q := by
              simpa only [Nat.succ_eq_add_one] using Nat.succ_le_of_lt hq
            have hdom : domain S.E S.hc (r0 + 2) .g1 ≤
                domain S.E S.hc q .g1 := by
              rw [domain_g1_eq_opening, domain_g1_eq_opening]
              exact base_opening_mono S hqge
            exact False.elim (hopen2 (hdom.trans hqHor))
          exact stableUserOutputsFrom_of_induction S rho b0 b1 s (r0 + 1) Pn.erase
            hexec.core hexec.interval.2.1 hmargin hout htransition1 hpost1 hK6all
      · have hpost0' : ∀ q, r0 < q → 0 < q →
            domain S.E S.hc q .g1 ≤ rho.horizon →
            PostOutageAboveTruncated S rho Pn.erase q := by
          intro q hq _ hqHor
          have hqge : r0 + 1 ≤ q := Nat.succ_le_of_lt hq
          have hdom : domain S.E S.hc (r0 + 1) .g1 ≤
              domain S.E S.hc q .g1 := by
            rw [domain_g1_eq_opening, domain_g1_eq_opening]
            exact base_opening_mono S hqge
          exact False.elim (hopen1 (hdom.trans hqHor))
        exact stableUserOutputsFrom_of_induction S rho b0 b1 s r0 Pn.erase hexec.core
          hexec.interval.2.1 hmargin hout htransition0 hpost0' hK6all
    rcases hrcCases with hrcPrev | hrcNow
    · have hrcG1Hor : domain S.E S.hc rc .g1 ≤ rho.horizon := by
        rw [hrcPrev]
        rw [domain_g1_eq_opening]
        have hopen0' : opening S.E S.hc r0 ≤ rho.horizon := by
          simpa only [domain_g1_eq_opening] using hopen0
        exact (base_opening_mono S (Nat.sub_le r0 1)).trans hopen0'
      have hcapNextHor : domain S.E S.hc (rc + 1) .g2 ≤ rho.horizon := by
        simpa only [hrcPrev, hprevSucc] using hdom0Hor
      have hcapClauses := outageCap_seed_clauses' S rho b0 b1 v s rc Pn hexec hmargin
        hsleep hv hstable hscope hno hconf hinv hrcpos hrcCap hcapNext hrcG1Hor
      have hcapState := outageMutualState_seed_at_cap_of_clauses S rho b0 b1 s rc Pn
        hexec hslash hmargin hsleep hno hheld0 hscope hrcpos hcapClauses.1
        hcapClauses.2.2 hcapClauses.2.1 hout hrcCap hcapNext hcapNextHor
      have hentryR0 : IntrinsicHighEntryHistory S rho Pn r0 := by
        simpa only [hrcPrev, hprevSucc] using
          entry_history_succ_of_carrierAbove S rho b0 b1 rc Pn hexec hscope hrcpos
            hcapClauses.1 hcapClauses.2.2
      have hK6opening : ∀ w ∈ rho.honest,
          Block.Preceq Pn.erase
              (Protocol.get_fg_root
                (NamedRun.readAt S rho (domain S.E S.hc r0 .g1) w).st.core.toHealing.toFG) ∨
            Pn.erase ∈ Internal.PhaseGrades.filteredTree
              (NamedRun.readAt S rho (domain S.E S.hc r0 .g1) w) := by
        intro w hw
        exact fgRootAbove_or_filtered_at_read_of_entry S rho b0 b1 s r0 Pn hexec
          hslash hmargin hsleep hscope hno hentryR0 hheld0 w hw
          (domain S.E S.hc r0 .g1) (by
            exact hb0cap.trans (by
              have hlt : b1 + S.E.Δ < domain S.E S.hc r0 .g2 := by
                simpa only [hrcPrev, hprevSucc] using hcapNext
              exact (hlt.trans (q10_domain_g2_lt_domain_g1 S r0)).le))
          (q10_domain_lt_a S r0 .g1)
      have hsgR0 : ∀ w ∈ rho.honest,
          let n := NamedRun.readAt S rho (domain S.E S.hc r0 .g1) w
          Block.Preceq Pn.erase n.st.core.F ∨
            ∃ raw : Block V,
              (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r0).g2 =
                some (some raw) ∧ Block.Preceq Pn.erase raw := by
        by_cases hearly : early S.E S.hc r0 .g2 < b1 + S.E.Δ
        · exact firstHealthy_sg_clause_of_retention' S rho b0 b1 v s r0 Pn hexec
            hslash hsleep hforming hv hmargin hstable hscope hno hconf hbudget hheld0
            hinv hr0 hhealthy hpredHealthy hearly hopen0
        · have hcapEarly : b1 + S.E.Δ ≤ early S.E S.hc r0 .g2 := le_of_not_gt hearly
          have hmaxPrev : max (S.a (r0 - 1)) S.E.t_GST ≤ b1 :=
            max_le hpredB1.le hexec.gst
          have hdeadlinePrev : max (S.a (r0 - 1)) S.E.t_GST + S.E.Δ ≤
              early S.E S.hc r0 .g2 :=
            (Int.add_le_add_right hmaxPrev S.E.Δ).trans hcapEarly
          have hdom0Nonneg : (0 : Time) ≤ domain S.E S.hc r0 .g1 := by
            rw [base_domain_g1_eq_opening]
            exact base_opening_nonneg S r0
          have hmajority0 : GradeFormingMajority S rho r0 :=
            hforming r0 hr0
              (Or.inr ⟨.g1, hdom0Nonneg, hopen0⟩)
          have hmajorityCap : GradeFormingMajority S rho (rc + 1) := by
            simpa only [hrcPrev, hprevSucc] using hmajority0
          have hstableCap : ∀ w ∈ rho.honest, Block.Preceq Pn.erase
              (Protocol.get_stable (NamedRun.stateBeforeTime S rho
                (domain S.E S.hc (rc + 1) .g2) w).st.core) := hcapState.2.1
          have hG2 := clause_at_g2_of_deadline S rho b0 b1 hexec Pn.erase rc
            (by simpa only [hrcPrev, hprevSucc] using hdeadlinePrev)
            hcapClauses.2.2 hstableCap hmajorityCap
          have hG2' : ∀ w ∈ rho.honest,
              Block.Preceq Pn.erase
                  (NamedRun.stateBeforeTime S rho
                    (domain S.E S.hc r0 .g2) w).st.core.F ∨
                ∃ raw, DecoupledConsensusModel.Protocol.freezeRoot S.E
                    (NamedRun.stateBeforeTime S rho
                      (domain S.E S.hc r0 .g2) w).st.core.toHealing.gradeView
                    (NamedRun.stateBeforeTime S rho
                      (domain S.E S.hc r0 .g2) w).st.core.F
                    S.hc.η_SG r0 (early S.E S.hc r0 .g2)
                    (late S.E S.hc r0 .g2) = some raw ∧
                  Block.Preceq Pn.erase raw := by
            intro w hw
            simpa only [hrcPrev, hprevSucc] using hG2 w hw hcapNextHor
          exact opening_sg_clause_of_g2_clause S rho hexec.core Pn.erase r0 hr0
            hG2' hK6opening hopen0
      have hjointR0 : S.a r0 ≤ rho.horizon → ∀ w ∈ rho.honest,
          Internal.NamedJointOutage.JointAt S rho Pn r0 w := by
        intro hact w hw
        exact jointAt_of_entry_history S rho b0 b1 s r0 Pn hexec hslash hmargin
          hsleep hscope hno hentryR0 hheld0
          (hexec.interval.2.1.trans hpost0) hact w hw
      have hcarR0 : HonestCarriersAbove S rho Pn.erase r0 :=
        carriersAbove_of_sg_clause S rho b0 b1 Pn r0 hexec hr0 hsgR0 hjointR0
      have hentryNext : IntrinsicHighEntryHistory S rho Pn (r0 + 1) :=
        entry_history_succ_of_carrierAbove S rho b0 b1 r0 Pn hexec hscope hr0
          hentryR0 hcarR0
      have hb0next : b0 ≤ domain S.E S.hc (r0 + 1) .g2 :=
        hb0cap.trans hdomNextCap.le
      have hprevSucc2 : r0 - 1 + 2 = r0 + 1 := by
        rw [show (2 : Nat) = 1 + 1 by norm_num, ← Nat.add_assoc, hprevSucc]
      have hviableNext := coverage_mutual_relativeG2_viability S rho b0 b1 s (r0 + 1)
        Pn hexec hslash hmargin hsleep hscope hno hentryNext hheld0 hb0next
      have hstableNextCap := coverage_mutual_stable_at_next_g2 S rho Pn.erase rc hexec.core
        hcapState.2.1
        (by simpa only [hrcPrev, hprevSucc2] using hviableNext)
        (by
          intro w hw k u huLo huHi he hpos hcut G hG hlat
          have hb0u : b0 ≤ u := by
            have hcapToR0 : b1 + S.E.Δ < domain S.E S.hc r0 .g2 := by
              simpa only [hrcPrev, hprevSucc] using hcapNext
            have hlow : b0 ≤ domain S.E S.hc r0 .g2 :=
              hb0cap.trans hcapToR0.le
            exact hlow.trans (by
              simpa only [hrcPrev, hprevSucc] using huLo)
          have huAction : u < S.a (r0 + 1) := by
            have hle := FrameForward.domain_le_a S (r0 + 1) .g2
            have huHi' : u < domain S.E S.hc (r0 + 1) .g2 := by
              simpa only [hrcPrev, hprevSucc2] using huHi
            exact huHi'.trans_le hle
          have hfg := coverage_mutual_fg_compatibility S rho b0 b1 s (r0 + 1) Pn
            hexec hslash hmargin hsleep hscope hno hentryNext hheld0 w hw u
            hb0u huAction
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
          exact confirmationDutyRoot_comparable_of_sg_clause S rho b0 b1 Pn r0
            hexec hr0 hsgR0 w hw u
            (by simpa only [hrcPrev, hprevSucc] using huLo)
            (by simpa only [hrcPrev, hprevSucc2] using huHi)
            hcut (hviableNext w hw) hfg hG')
      have hstateR0 : OutageMutualStateAt S rho Pn b0 s r0 := by
        have hinvR0 := outageInvariant_seed S rho b0 b1 s r0 Pn hexec hscope hr0
          hcarR0 hentryR0
        have hstableR0 : OutageStableAtNextG2 S rho Pn.erase r0 := by
          unfold OutageStableAtNextG2
          simpa only [hrcPrev, hprevSucc2] using hstableNextCap
        exact ⟨hinvR0, hstableR0, hsgR0⟩
      exact finish hstateR0
    · have hcapClauses := outageCap_seed_clauses' S rho b0 b1 v s rc Pn hexec hmargin
        hsleep hv hstable hscope hno hconf hinv hrcpos hrcCap hcapNext
        (by simpa only [hrcNow] using hopen0)
      by_cases hopen1Now : domain S.E S.hc (r0 + 1) .g1 ≤ rho.horizon
      · have hdomNextHor : domain S.E S.hc (r0 + 1) .g2 ≤ rho.horizon :=
          (q10_domain_g2_lt_domain_g1 S (r0 + 1)).le.trans hopen1Now
        have hcapState := outageMutualState_seed_at_cap_of_clauses S rho b0 b1 s rc Pn
          hexec hslash hmargin hsleep hno hheld0 hscope hrcpos hcapClauses.1
          hcapClauses.2.2 hcapClauses.2.1 hout hrcCap hcapNext
          (by simpa only [hrcNow] using hdomNextHor)
        exact finish (by simpa only [hrcNow] using hcapState)
      · have hentryShort : ∀ q : Round, 0 < q → q ≤ r0 + 1 →
            IntrinsicHighEntryHistory S rho Pn q := by
          intro q hq hqle
          by_cases hle : q ≤ r0
          · exact hentryBefore q hq hle
          · have hqeq : q = r0 + 1 := Nat.le_antisymm hqle
              (Nat.succ_le_of_lt (Nat.lt_of_not_ge hle))
            have hentryR0 : IntrinsicHighEntryHistory S rho Pn r0 := by
              simpa only [hrcNow] using hcapClauses.1
            have hcarR0 : HonestCarriersAbove S rho Pn.erase r0 := by
              simpa only [hrcNow] using hcapClauses.2.2
            have hsucc := entry_history_succ_of_carrierAbove S rho b0 b1 r0 Pn
              hexec hscope hr0 hentryR0 hcarR0
            simpa only [hqeq] using hsucc
        have hK6allShort : ∀ t, b0 ≤ t → t ≤ rho.horizon → ∀ w ∈ rho.honest,
            Block.Preceq Pn.erase
                (Protocol.get_fg_root
                  (NamedRun.readAt S rho t w).st.core.toHealing.toFG) ∨
              Pn.erase ∈ Internal.PhaseGrades.filteredTree (NamedRun.readAt S rho t w) := by
          intro t ht0 hth w hw
          let q := clockRoundAt S t + 1
          have hq : 0 < q := Nat.succ_pos _
          have hqt : t < S.a q :=
            (clockRound_lt_opening_succ S t).trans_le (incl_opening_le_a S q)
          have htlt : t < domain S.E S.hc (r0 + 1) .g1 := by
            apply lt_of_not_ge
            intro h
            exact hopen1Now (h.trans hth)
          have htlt' : t < opening S.E S.hc (r0 + 1) := by
            simpa only [domain_g1_eq_opening] using htlt
          have ht0' : (0 : Time) ≤ t := by
            have h6 : (0 : Time) ≤ 6 * S.E.Δ :=
              Int.mul_nonneg (by norm_num) S.E.Δ_pos.le
            exact h6.trans (six_delta_lt_b0 S s b0 hmargin).le |>.trans ht0
          have hclock : clockRoundAt S t < r0 + 1 := by
            by_contra hnot
            have hge : r0 + 1 ≤ clockRoundAt S t := Nat.le_of_not_gt hnot
            have hopen := base_opening_mono S hge
            exact (not_lt_of_ge (hopen.trans (opening_le_clockRound S t ht0')) htlt')
          have hqle : q ≤ r0 + 1 := by
            dsimp only [q]
            exact Nat.succ_le_of_lt hclock
          exact fgRootAbove_or_filtered_at_read_of_entry S rho b0 b1 s q Pn hexec
            hslash hmargin hsleep hscope hno (hentryShort q hq hqle) hheld0 w hw t ht0 hqt
        have hsgsShort : TransitionSGClauses S rho b0 Pn r0 := by
          intro q hq hqle w hw
          by_cases hqprev : q ≤ r0 - 1
          · exact hsgsBefore q hq hqprev w hw
          · have hqeq : q = r0 := by
              have hle' : q ≤ (r0 - 1) + 1 := by
                simpa only [hprevSucc] using hqle
              have hge : r0 ≤ q := by
                simpa only [Nat.succ_eq_add_one, hprevSucc] using
                  (Nat.succ_le_of_lt (Nat.lt_of_not_ge hqprev))
              exact Nat.le_antisymm (by simpa only [hprevSucc] using hle') hge
            simpa only [hqeq, hrcNow] using hcapClauses.2.1 w hw
        have htransitionShort := stableUserOutputs_transition_of_sg S rho b0 b1 s r0 Pn
          hexec.core hexec.interval.2.1 hmargin hsgsShort hconf.2.2 hout hK6allShort
        have hpostShort : ∀ q, r0 < q → 0 < q →
            domain S.E S.hc q .g1 ≤ rho.horizon →
            PostOutageAboveTruncated S rho Pn.erase q := by
          intro q hq _ hqHor
          have hqge : r0 + 1 ≤ q := Nat.succ_le_of_lt hq
          have hdom : domain S.E S.hc (r0 + 1) .g1 ≤
              domain S.E S.hc q .g1 := by
            rw [domain_g1_eq_opening, domain_g1_eq_opening]
            exact base_opening_mono S hqge
          exact False.elim (hopen1Now (hdom.trans hqHor))
        exact stableUserOutputsFrom_of_induction S rho b0 b1 s r0 Pn.erase hexec.core
          hexec.interval.2.1 hmargin hout htransitionShort hpostShort hK6allShort
  · have hK6allShort : ∀ t, b0 ≤ t → t ≤ rho.horizon → ∀ w ∈ rho.honest,
        Block.Preceq Pn.erase
            (Protocol.get_fg_root
              (NamedRun.readAt S rho t w).st.core.toHealing.toFG) ∨
          Pn.erase ∈ Internal.PhaseGrades.filteredTree (NamedRun.readAt S rho t w) := by
      intro t ht0 hth w hw
      let q := clockRoundAt S t + 1
      have hq : 0 < q := Nat.succ_pos _
      have hqt : t < S.a q :=
        (clockRound_lt_opening_succ S t).trans_le (incl_opening_le_a S q)
      have htlt : t < domain S.E S.hc r0 .g1 := by
        apply lt_of_not_ge
        intro h
        exact hopen0 (h.trans hth)
      have htlt' : t < opening S.E S.hc r0 := by
        simpa only [domain_g1_eq_opening] using htlt
      have ht0' : (0 : Time) ≤ t := by
        have h6 : (0 : Time) ≤ 6 * S.E.Δ :=
          Int.mul_nonneg (by norm_num) S.E.Δ_pos.le
        exact h6.trans (six_delta_lt_b0 S s b0 hmargin).le |>.trans ht0
      have hclock : clockRoundAt S t < r0 := by
        by_contra hnot
        have hge : r0 ≤ clockRoundAt S t := Nat.le_of_not_gt hnot
        have hopen := base_opening_mono S hge
        exact (not_lt_of_ge (hopen.trans (opening_le_clockRound S t ht0')) htlt')
      have hqle : q ≤ r0 := by
        dsimp only [q]
        exact Nat.succ_le_of_lt hclock
      exact fgRootAbove_or_filtered_at_read_of_entry S rho b0 b1 s q Pn hexec
        hslash hmargin hsleep hscope hno (hentryBefore q hq hqle) hheld0 w hw t ht0 hqt
    have htransitionBefore := stableUserOutputs_transition_of_sg S rho b0 b1 s (r0 - 1)
      Pn hexec.core hexec.interval.2.1 hmargin hsgsBefore hconf.2.2 hout hK6allShort
    have hpostBefore : ∀ q, r0 - 1 < q → 0 < q →
        domain S.E S.hc q .g1 ≤ rho.horizon →
        PostOutageAboveTruncated S rho Pn.erase q := by
      intro q hq _ hqHor
      have hqge : r0 ≤ q := by
        simpa only [Nat.succ_eq_add_one, hprevSucc] using Nat.succ_le_of_lt hq
      have hdom : domain S.E S.hc r0 .g1 ≤ domain S.E S.hc q .g1 := by
        rw [domain_g1_eq_opening, domain_g1_eq_opening]
        exact base_opening_mono S hqge
      exact False.elim (hopen0 (hdom.trans hqHor))
    exact stableUserOutputsFrom_of_induction S rho b0 b1 s (r0 - 1) Pn.erase
      hexec.core hexec.interval.2.1 hmargin hout htransitionBefore hpostBefore hK6allShort


#print axioms stable_chain_outage_resilience_of_clauses''

theorem stable_chain_outage_resilience_from_output_seed
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s : Round) (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hseed : OutputSeed S rho b0 s P) (hs : 0 < s)
    (hretention : StableRetentionBudget S rho v s P b1) :
    StableUserOutputsFrom S rho b0 P := by
  have h1 := stableAt_honestConfirmedAtOrAbove
    S rho b0 b1 v s P hexec hslash hcom hsleep hforming hv hmargin hseed hs
  have hconf := honestConfirmedAbove_of_base_clauses'
    S rho b0 b1 v s P hexec hslash hsleep hforming hv hmargin
      hseed hretention hseed.noConflict h1
  exact stable_chain_outage_resilience_of_clauses''
    S rho b0 b1 v s P hexec hslash hcom hsleep hforming hv hmargin
      hseed hretention hseed.noConflict hconf

#print axioms stable_chain_outage_resilience_from_output_seed


/-- The historical stableAt-seeded form ( fallback premise), kept as an
explicit statement now that the public statement is seeded by the stable
output. -/
theorem stable_chain_outage_resilience_stableAt_seed (S : Setup V) :
    ∀ rho b0 b1 v s P,
      OutageExecution S rho b0 b1 → NamedOutageEntry.SlashableBound S rho →
      HonestCommittees S rho.honest → OutageSleepyThroughout S rho →
      GradeFormingThroughout S rho → v ∈ rho.honest → FormationMargin S s b0 →
      stableAt S rho v s P → RetentionDuration S rho s b1 →
      StableUserOutputsFrom S rho b0 P := by
  intro rho b0 b1 v s P hexec hslash hcom hsleep hforming hv hmargin hstable hretention
  have hs : 0 < s := stableAt_round_pos S hexec.core hstable
  have hseed := outputSeed_of_stableAt
    S rho b0 b1 v s P hexec hslash hcom hsleep hforming hv hmargin hstable hs
  exact stable_chain_outage_resilience_from_output_seed
    S rho b0 b1 v s P hexec hslash hcom hsleep hforming hv hmargin hseed hs hretention

#print axioms stable_chain_outage_resilience_stableAt_seed

/-- The round-action form of the output-seeded theorem: the stable output read at
the round-`s` action itself, with the round-form margins. -/
def StableOutputOutageResilienceAtAction (S : Setup V) : Prop :=
  ∀ rho b0 b1 v s P,
    OutageExecution S rho b0 b1 → NamedOutageEntry.SlashableBound S rho →
    HonestCommittees S rho.honest → OutageSleepyThroughout S rho →
    GradeFormingThroughout S rho → v ∈ rho.honest → FormationMargin S s b0 →
    Block.Preceq P (Protocol.get_stable (Run.storeAt S rho v (S.a s)).core) →
    RetentionDuration S rho s b1 → StableUserOutputsFrom S rho b0 P

/-- Any time `T` at or before the round-`s` action: the full proof-layer
conclusion from the stable output read at `T`. -/
theorem stableUserOutputsFrom_of_output_at
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V) (s : Round) (T : Time)
    (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hTs : T ≤ S.a s) (hmargin : FormationMargin S s b0)
    (houtput : Block.Preceq P (Protocol.get_stable (Run.storeAt S rho v T).core))
    (hretention : RetentionDuration S rho s b1) :
    StableUserOutputsFrom S rho b0 P := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · have hroundOne : domain S.E S.hc 1 .g2 ≤ b0 :=
      (FrameForward.domain_le_a S 1 .g2).trans
        ((Assembly.a_mono S (Nat.succ_le_succ (Nat.zero_le 0))).trans
          ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin))
    have hT1 := protectedVoteSlots_before S rho b0 b1 hexec hcom hsleep hroundOne
    have hconf := namedConfirmationIdxQueryEmitted_of_healthyPrefix_of_T1
      S rho b0 b1 hexec hcom hsleep hroundOne hT1
    obtain ⟨C, hhistory⟩ :=
      NamedOutageHistory.OutageEnv.layerA_joint_history_idx_emitted_of_outage
        S rho b0 b1 0 hexec hsleep hmargin hcom hconf
        (boundaryIdx rho b0) (le_refl _)
    obtain ⟨_, hsource⟩ := stableOutput_sourceBefore_at
      S rho b0 b1 hexec hcom hsleep v hv 0 T hTs hmargin C hhistory P houtput
    have hPgen : P = Block.genesis := by
      rcases hsource with hgen | hsource
      · exact hgen
      · unfold SourceBefore at hsource
        rcases hsource with ⟨k, hk, x, hx, hsrc⟩
        exact False.elim (Nat.not_lt_zero _ hk)
    subst P
    intro w hw t ht0 hth
    refine ⟨Protocol.preceq_genesis _, ?_, ?_⟩
    · intro G hG
      exact Protocol.preceq_genesis _
    · intro u hu0 hut B hB
      exact Protocol.preceq_genesis _
  · have hseed := stableOutput_seed_at
      S rho b0 b1 hexec hcom hsleep hforming v hv s hs T hTs hmargin P houtput
    exact stable_chain_outage_resilience_from_output_seed
      S rho b0 b1 v s P hexec hslash hcom hsleep hforming hv hmargin hseed hs hretention

#print axioms stableUserOutputsFrom_of_output_at

theorem stable_output_outage_resilience_at_action (S : Setup V) :
    StableOutputOutageResilienceAtAction S := by
  intro rho b0 b1 v s P hexec hslash hcom hsleep hforming hv hmargin houtput hretention
  exact stableUserOutputsFrom_of_output_at S rho b0 b1 v s (S.a s) P hexec hslash hcom hsleep
    hforming hv (le_refl _) hmargin houtput hretention

#print axioms stable_output_outage_resilience_at_action


/-- Public stable-chain outage resilience: seeded by the stable output at
any time `T`, in time form, with the output-only conclusion. -/
theorem stable_chain_outage_resilience_public (S : Setup V) :
    StableChainOutageResilience S := by
  intro rho b0 b1 T v P hexec hslash hcom hawake hv hmargin houtput hret hhor
  have hsleep := outageSleepyThroughout_of_awake S rho hawake
  have hforming := gradeFormingThroughout_of_awake S rho
    hexec.execution.toNamedScheduleWellFormed hawake
  have hmargin' := formationMargin_of_time S T b0 hmargin
  have hretention := retentionDuration_of_time S rho T b1 hret hhor
  have hall := stableUserOutputsFrom_of_output_at S rho b0 b1 v (roundAfter S T) T P
    hexec hslash hcom hsleep hforming hv (le_nextAction S T) hmargin' houtput hretention
  intro w hw t ht0 hth
  exact (hall w hw t ht0 hth).1

#print axioms stable_chain_outage_resilience_public

#print axioms stable_chain_outage_resilience_public

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
