module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.Premises
public import DecoupledConsensusProofs.Execution.RoundBase
public import DecoupledConsensusProofs.Protocol.Grades.Interpolation
public import DecoupledConsensusProofs.Execution.OutageInputs
public import DecoupledConsensusProofs.Protocol.Grades.HealthyHeadReady
public import DecoupledConsensusProofs.Execution.Runtime
public import DecoupledConsensusProofs.Protocol.Handlers.BlockStamp
public import DecoupledConsensusProofs.Execution.BoundaryHolding
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.IntrinsicEntry
public import DecoupledConsensusProofs.Protocol.Handlers.FGProtection
public import DecoupledConsensusProofs.Execution.OutputSeedCore

@[expose] public section

/-!
# Stage 2: clause 2 of the pre-outage premise from the healthy prefix

`HonestHeadHeldAbove` discharged from `OutageExecution` and clause 1
(`HonestConfirmedAtOrAbove`), with no further premise.

The route has three steps. The emitter's own action read holds a body whose
root is the confirmed root (`Proofs.NamedOutageInputs.emitted_attestation_head`).
That body membership is stated at the STAGED INDEX read
`actionReadFrom S (NamedRun.stateBefore S rho i v) a.round`; the staging only
sets the clock and runs the confirmation duty, neither of which touches
`st.bodies`, so it transfers to `NamedRun.stateBefore S rho i v`, and
`Proofs.NamedRuntime.tick_prefix_eq_strict` turns that into the TIME read
`NamedRun.stateBeforeTime S rho t v`. Clause 1, applied at the same action with
`K:= H`, puts `P` below `H.erase`; composed with the clause's own guard
`F(cut) ⪯ P` that is the finalized-prefix hypothesis of
`NamedHealthyHeadReady.healthy_head_body_at_read`, whose three time hypotheses
are exactly `le_rfl`, the clause's `t + Δ ≤ cut` and the clause's `t + Δ ≤ b0`.
The returned holding, the returned stamp at `t + Δ` pushed up by
`occurrenceBefore_mono`, and the root equation finish the three conjuncts.
-/
namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The staged action read does not touch the bodies: `actionReadFrom` sets the
clock and runs `update_confirmation_with`, and the named form of the latter
rewrites only the `core` field. -/
private theorem actionReadFrom_bodies (S : Setup V) (n : NamedNodeState V) (r : Round) :
    (actionReadFrom S n r).st.bodies = n.st.bodies := rfl

/-- Arithmetic core over bare `Int`: `omega` refuses a goal stated at the `Time`
alias and cannot see `Δ_pos`, so the margin-to-strict step is stated here. -/
private theorem lt_of_add_pos_le : ∀ x d b : Int, 0 < d → x + d ≤ b → x < b := by
  intro x d b hd h
  omega


/-- Stage 2, clause 2 (addendum 34 17). The emitter's
confirmed head is held at every honest reader from one delay after the action,
compatible with that reader's finalized block and stamped before the read,
whenever the reader's finalized block has not passed `P`. -/
theorem stage2_honestHeadHeldAbove (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (s : Round) (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (hconf1 : HonestConfirmedAtOrAbove S rho b0 s P) :
    HonestHeadHeldAbove S rho b0 s P := by
  intro a t ha hem hmargin hround reader hreader cut hcut hFP key hkey
  -- Step 1: the emitter-side body, at the staged index read.
  obtain ⟨i, hi, _, H, hH, hroot⟩ := Proofs.NamedOutageInputs.emitted_attestation_head S rho hem
  -- Bridge A1: the staging leaves `st.bodies` alone.
  have hHindex : H ∈ (NamedRun.stateBefore S rho i a.val_index).st.bodies := by
    rw [← actionReadFrom_bodies S (NamedRun.stateBefore S rho i a.val_index) a.round]
    exact hH
  -- Bridge A2: the index read at a witnessed tick is the strict time read.
  have hstate : NamedRun.stateBefore S rho i a.val_index =
      NamedRun.stateBeforeTime S rho t a.val_index :=
    Proofs.NamedRuntime.tick_prefix_eq_strict S rho hexec.core.sorted hexec.core.nodup hi
  have hHsource : H ∈ (NamedRun.stateBeforeTime S rho t a.val_index).st.bodies := by
    rw [← hstate]; exact hHindex
  -- Step 2: `P ⪯ H.erase`, from clause 1 at the same action with `K:= H`.
  have hscope : NamedRun.blockInRun S rho H :=
    Proofs.NamedRuntime.blockInRun_of_direct S rho (Or.inr ⟨a.val_index, ha, i, hHindex⟩)
  have hkeyH : H.root = key := Option.some.inj (hroot.symm.trans hkey)
  have htlt : t < b0 := lt_of_add_pos_le t S.E.Δ b0 S.E.Δ_pos hmargin
  have hPH : Block.Preceq P H.erase := hconf1 a t ha hem htlt hround key hkey H hscope hkeyH
  -- Step 3: the held body and the stamp, from the healthy prefix.
  have hF : Block.Preceq (NamedRun.stateBeforeTime S rho cut reader).st.core.F H.erase :=
    Block.preceq_trans hFP hPH
  obtain ⟨hheld, hstamp, _⟩ :=
    NamedHealthyHeadReady.healthy_head_body_at_read S rho hexec.core b0 hexec.healthy
      a.val_index ha reader hreader H t (t + S.E.Δ) cut hHsource le_rfl hcut hmargin hF
  -- Step 4: the three conjuncts.
  refine ⟨H, hheld, hkeyH, ?_, ?_⟩
  · -- `Block.compatible B C = preceq B C || preceq C B`, and we have the second.
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr hF
  · intro gamma hgamma
    rw [stampedBefore_eq_occurrenceBefore] at hstamp ⊢
    exact occurrenceBefore_mono hgamma hstamp

#print axioms stage2_honestHeadHeldAbove



/-- Round arithmetic: a round strictly above `s + 1` is positive and strictly
above `s`. -/
private theorem stage2_round_bounds : ∀ s q : Nat, s + 1 < q → 0 < q ∧ s < q := by
  intro s q h
  exact ⟨by omega, by omega⟩

/-- **The pre-boundary frame clause above the stable round's successor.** Every honest reader's
opening read of a round `q` with `s + 1 < q` whose action is before the outage
either has the protected prefix at or below its finalized block, or carries a
round-`q` grade-2 frame result covering it.

`hPn` is NOT in the list: the named representative of the protected prefix that
every downstream lemma consumes is the one `stable_prefix_held_at_boundary`
returns, which carries its own `blockInRun`. The protected prefix enters only as
the erased block `Pn.erase`. -/
theorem stage2_preBoundaryFrames_above (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (v : V) (s : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hsleep : OutageSleepyThroughout S rho) (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hseed : OutputSeed S rho b0 s Pn.erase)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hconf1 : HonestConfirmedAtOrAbove S rho b0 s Pn.erase)
    (hconf2 : HonestHeadHeldAbove S rho b0 s Pn.erase)
    (hbudget : StableRetentionBudget S rho v s Pn.erase b1) :
    ∀ w ∈ rho.honest, ∀ q : Round, s + 1 < q → S.a q < b0 →
      let n := NamedRun.readAt S rho (domain S.E S.hc q .g1) w
      Block.Preceq Pn.erase n.st.core.F ∨
        ∃ raw : Block V,
          (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing q).g2 = some (some raw) ∧
            Block.Preceq Pn.erase raw := by
  -- The named representative of the protected prefix that is held everywhere at
  -- the boundary. Everything downstream runs on it.
  obtain ⟨Pm, hPe, hscope, hheld0⟩ := NamedBoundaryHolding.stable_prefix_held_at_boundary
    S rho b0 b1 hexec hsleep v hv s Pn.erase hmargin hseed hno
  rw [← hPe] at hseed hno hconf1 hconf2 hbudget
  intro w hw q hgap hqb0
  show Block.Preceq Pn.erase
      (NamedRun.readAt S rho (domain S.E S.hc q .g1) w).st.core.F ∨
    ∃ raw : Block V,
      (DecoupledConsensusModel.Protocol.readFrame (NamedRun.readAt S rho (domain S.E S.hc q .g1) w).cache
        (NamedRun.readAt S rho (domain S.E S.hc q .g1) w).st.core.toHealing q).g2 =
          some (some raw) ∧
      Block.Preceq Pn.erase raw
  rw [← hPe]
  obtain ⟨hqpos, hsq⟩ := stage2_round_bounds s q hgap
  -- The three schedule bounds. The round's whole phase schedule sits at or
  -- before its action, which is strictly before the boundary.
  have hfirst : S.a (q - 1) < b0 :=
    lt_of_le_of_lt (Assembly.a_mono S (Nat.sub_le q 1)) hqb0
  have hg1b0 : domain S.E S.hc q .g1 ≤ b0 :=
    (FrameForward.domain_le_a S q .g1).trans (le_of_lt hqb0)
  have hhor : domain S.E S.hc q .g1 ≤ rho.horizon :=
    hg1b0.trans (hexec.interval.2.1.trans hexec.interval.2.2)
  have hrb1 : domain S.E S.hc q .g2 ≤ b1 + S.E.Δ :=
    (((FrameForward.domain_le_a S q .g2).trans (le_of_lt hqb0)).trans hexec.interval.2.1).trans
      (le_add_of_nonneg_right S.E.Δ_pos.le)
  -- The two intrinsic history premises, both from the pre-boundary cut.
  have hentry : IntrinsicHighEntryHistory S rho Pm q :=
    Proofs.NamedIntrinsicEntry.initial_intrinsic_history S rho b0 Pm q hscope hno hfirst
  have hband : IntrinsicConflictingCarrierBand S rho Pm q :=
    NamedConflictingCarrierBand.intrinsic_conflicting_carrier_band S rho b0 b1 s q Pm hexec
      hmargin hsleep hentry
  exact sg_at_domain_read_of_common_support_at S rho b0 b1 s q Pm hexec hslash hsleep hforming
    hscope hqpos hsq hhor hmargin hno hband hentry hheld0
    (base_hpost S rho b0 q Pm hfirst) ⟨hconf1, hconf2⟩ v hv hseed
    (common_support_base_at S rho b0 b1 v s q Pm hexec hsleep hforming hv hmargin hseed
      hscope hno hconf1 hconf2 hbudget hentry hqpos hgap hrb1 hfirst) w hw

#print axioms stage2_preBoundaryFrames_above





private theorem stage2_le_of_add_le : ∀ x d b : Int, 0 < d → x + d ≤ b → x ≤ b := by
  intro x d b hd h
  omega

private theorem stage2_succ_le_add_six : ∀ x d : Int, 0 < d → x + 1 ≤ x + 6 * d := by
  intro x d hd
  omega

private theorem stage2_early_le_late (S : Setup V) (r : Round) :
    early S.E S.hc r .g2 ≤ late S.E S.hc r .g2 := by
  have h : ∀ x d : Int, 0 < d → x + -5 * d ≤ x + -1 * d := by
    intro x d hd
    omega
  simpa only [early, late, Phase.earlyOffset, Phase.lateOffset] using
    h (opening S.E S.hc r) S.E.Δ S.E.Δ_pos

private theorem stage2_opening_cut_le_a (S : Setup V) (r : Round) :
    domain S.E S.hc r .g1 + 1 ≤ S.a r := by
  have he : S.a r = domain S.E S.hc r .g1 + 6 * S.E.Δ := by
    unfold Setup.a Protocol.HealConfig.a domain opening Phase.domainOffset
      Protocol.proposal_time Env.t slotStart
    ring
  rw [he]
  exact stage2_succ_le_add_six _ _ S.E.Δ_pos

private theorem stage2_g2_lt_opening_cut (S : Setup V) (r : Round) :
    domain S.E S.hc r .g2 < domain S.E S.hc r .g1 + 1 :=
  Int.lt_add_one_iff.mpr (by rw [incl_domain_g1_eq_opening]; exact domain_le_opening S r)

/-- Arithmetic over bare `Nat`: `omega` will not read a goal stated at the
`Round` abbreviation. -/
private theorem stage2_window_lo : ∀ s e : Nat, 1 ≤ e → s + 1 - e ≤ s := by
  intro s e h
  omega

/-- The stable round is in round `s + 1`'s support window: `η_SG ≥ 1`. -/
private theorem stage2_stable_in_window (S : Setup V) (s : Round) :
    s ∈ Protocol.latest_window S.hc.η_SG (s + 1) :=
  mem_latest_window (stage2_window_lo s S.hc.η_SG S.hc.η_SG_ge_one) (Nat.lt_succ_self s)

/-- The formation margin bounds round `s + 1`'s whole schedule by the boundary. -/
private theorem stage2_a_succ_le (S : Setup V) (s : Round) (b0 : Time)
    (hmargin : FormationMargin S s b0) : S.a (s + 1) ≤ b0 := by
  have hm : S.a (s + 1) + S.E.Δ ≤ b0 := hmargin
  exact stage2_le_of_add_le _ _ _ S.E.Δ_pos hm

/-- **The round-`s` row of an honest round-`s` voter, ready at round `s + 1`'s
G2 early cutoff.** `HealthySGArrival` states the delivered row at the read
`domain (s+1).g2` with its projection stamp before `early (s+1).g2`, which is
exactly the phase read and cutoff the round-`(s+1)` grade uses; clause 2 makes
the body ready there. -/
private theorem stage2_voter_early_input (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (s : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hhead : HonestHeadHeldAbove S rho b0 s Pn.erase)
    (w : V) (hw : w ∈ rho.honest)
    (hFP : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc (s + 1) .g2) w).st.core.F Pn.erase)
    (u : V) (hu : u ∈ honestRoundVoters S rho s) :
    ∃ c : NamedAttestation V, c.round = s ∧
      Protocol.sgVote c.erase ∈ DecoupledConsensusModel.Protocol.interpretedInputs
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc (s + 1) .g2) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc (s + 1) .g2) w).st.core.F
        S.hc.η_SG (s + 1) (early S.E S.hc (s + 1) .g2) u := by
  have sch := hexec.core.toNamedScheduleWellFormed
  have roots := hexec.core.toNamedRootCollisionFree
  have hR : 3 ≤ S.hc.R := S.hc.R_ge_three
  have harr : HealthySGArrival S rho b0 := healthySGArrival_of_exec S rho b0 b1 hexec
  have hopen : opening S.E S.hc (s + 1) ≤ b0 :=
    (incl_opening_le_a S (s + 1)).trans (stage2_a_succ_le S s b0 hmargin)
  obtain ⟨c, hcval, hcround, hcem, hcdead, hcraw⟩ :=
    rawInputs_mem_of_vote S rho sch harr hR s (s + 1) u hu (stage2_stable_in_window S s)
      (Nat.lt_succ_self s) hopen w hw
  have hcrlt : c.round < s + 1 := by rw [hcround]; exact Nat.lt_succ_self s
  have hcready := retained_bodyReady S rho sch roots b0 s Pn.erase hhead w hw u
    (Finset.mem_filter.mp hu).1 hcval (le_of_eq hcround.symm) hcdead hcem
    (domain S.E S.hc (s + 1) .g2) (early S.E S.hc (s + 1) .g2)
    ((action_delta_le_early S hR hcrlt).trans (early_le_domain S (s + 1))) hFP
    (action_delta_le_early S hR hcrlt)
  exact ⟨c, hcround, Finset.mem_filter.mpr ⟨hcraw, hcready⟩⟩

/-- **The supporter inclusion at the formation round.** -/
private theorem stage2_voters_positive (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (s : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hconf : HonestConfirmedAtOrAbove S rho b0 s Pn.erase)
    (hhead : HonestHeadHeldAbove S rho b0 s Pn.erase)
    (w : V) (hw : w ∈ rho.honest)
    (hFP : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc (s + 1) .g2) w).st.core.F Pn.erase) :
    honestRoundVoters S rho s ⊆ Finset.univ.filter (fun u => positive
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc (s + 1) .g2) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc (s + 1) .g2) w).st.core.F
      S.hc.η_SG (s + 1) (early S.E S.hc (s + 1) .g2) (late S.E S.hc (s + 1) .g2) u
      Pn.erase = true) := by
  have sch := hexec.core.toNamedScheduleWellFormed
  have auth := hexec.core.toNamedUnforgeable
  have roots := hexec.core.toNamedRootCollisionFree
  have hR : 3 ≤ S.hc.R := S.hc.R_ge_three
  have hfirst : S.a (s + 1 - 1) < b0 := by
    simpa only [Nat.add_sub_cancel] using
      lt_of_add_pos_le (S.a s) S.E.Δ b0 S.E.Δ_pos
        (le_trans (Int.add_le_add_right (Assembly.a_mono S (Nat.le_succ s)) S.E.Δ) hmargin)
  intro u hu
  have huh : u ∈ rho.honest := (Finset.mem_filter.mp hu).1
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ u, ?_⟩
  obtain ⟨c, hcround, hcinterp⟩ :=
    stage2_voter_early_input S rho b0 b1 s Pn hexec hmargin hhead w hw hFP u hu
  obtain ⟨y, hy, hymax⟩ := Finset.exists_max_image
    (DecoupledConsensusModel.Protocol.interpretedInputs
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc (s + 1) .g2) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc (s + 1) .g2) w).st.core.F
      S.hc.η_SG (s + 1) (early S.E S.hc (s + 1) .g2) u)
    (fun z : Protocol.SGVote V => z.round) ⟨_, hcinterp⟩
  have hyraw : y ∈ DecoupledConsensusModel.Protocol.rawInputs
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc (s + 1) .g2) w).st.core.toHealing.gradeView
      S.hc.η_SG (s + 1) (early S.E S.hc (s + 1) .g2) u := (Finset.mem_filter.mp hy).1
  have hys : s ≤ y.round := by
    have := hymax _ hcinterp
    rw [sgVote_round, hcround] at this
    exact this
  refine decide_eq_true ⟨DecoupledConsensusModel.Protocol.token y, Finset.mem_image_of_mem _ hy,
    ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hz
    exact hymax _ hz'
  · exact rawInputs_localCovers S rho sch auth roots hR b0 s (s + 1) Pn hconf hhead hfirst
      hexec.boundaryPublic w hw hFP u huh (early S.E S.hc (s + 1) .g2) hyraw hys
  · intro tx htx ty hty _ hround
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp htx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hty
    obtain ⟨p, _, hpround, hpproj, _, _, hpem⟩ :=
      rawInputs_trace S rho sch auth (domain S.E S.hc (s + 1) .g2)
        (late S.E S.hc (s + 1) .g2) w S.hc.η_SG (s + 1) u huh hx'
    obtain ⟨q, _, hqround, hqproj, _, _, hqem⟩ :=
      rawInputs_trace S rho sch auth (domain S.E S.hc (s + 1) .g2)
        (late S.E S.hc (s + 1) .g2) w S.hc.η_SG (s + 1) u huh hy'
    have hpq : p = q := NamedOutageProvenance.emitted_same_round_unique S rho sch hpem hqem
      (by rw [hpround, hqround]; exact hround)
    show x'.confirmed = y'.confirmed
    rw [← hpproj, ← hqproj, hpq]
  · intro tz htz hltz
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp htz
    have hzraw : z' ∈ DecoupledConsensusModel.Protocol.rawInputs
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc (s + 1) .g2) w).st.core.toHealing.gradeView
        S.hc.η_SG (s + 1) (late S.E S.hc (s + 1) .g2) u := (Finset.mem_filter.mp hz').1
    exact rawInputs_localCovers S rho sch auth roots hR b0 s (s + 1) Pn hconf hhead hfirst
      hexec.boundaryPublic w hw hFP u huh (late S.E S.hc (s + 1) .g2) hzraw
      (le_of_lt (lt_of_le_of_lt hys hltz))

/-- **The opposition inclusion at the formation round.** Every honest opponent
of the protected prefix at the round-`(s+1)` G2 phase read is a stale historical
voter of round `s + 1`. There is no inventory read: the non-covering late row
comes from a round strictly below `s` (`rawInputs_localCovers` rules out `s` and
above), and the opponent cannot also have voted in round `s`, because that row
is in the reader's EARLY view by `HealthySGArrival` and would break the
domination clause of `Opposes`. -/
private theorem stage2_opposition_stale (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (s : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hconf : HonestConfirmedAtOrAbove S rho b0 s Pn.erase)
    (hhead : HonestHeadHeldAbove S rho b0 s Pn.erase)
    (w : V) (hw : w ∈ rho.honest)
    (hFP : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc (s + 1) .g2) w).st.core.F Pn.erase) :
    Finset.univ.filter (fun u => opposing
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc (s + 1) .g2) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc (s + 1) .g2) w).st.core.F
      S.hc.η_SG (s + 1) (early S.E S.hc (s + 1) .g2) (late S.E S.hc (s + 1) .g2) u
      Pn.erase = true) ⊆
      (Finset.univ \ rho.honest) ∪ staleHistoricalVoters S rho (s + 1) := by
  have sch := hexec.core.toNamedScheduleWellFormed
  have auth := hexec.core.toNamedUnforgeable
  have roots := hexec.core.toNamedRootCollisionFree
  have hR : 3 ≤ S.hc.R := S.hc.R_ge_three
  have hfirst : S.a (s + 1 - 1) < b0 := by
    simpa only [Nat.add_sub_cancel] using
      lt_of_add_pos_le (S.a s) S.E.Δ b0 S.E.Δ_pos
        (le_trans (Int.add_le_add_right (Assembly.a_mono S (Nat.le_succ s)) S.E.Δ) hmargin)
  intro u hu
  by_cases huh : u ∈ rho.honest
  · refine Finset.mem_union_right _ ?_
    have hopp := (Finset.mem_filter.mp hu).2
    simp only [opposing, decide_eq_true_eq] at hopp
    rcases hopp with ⟨x, hx, hdom, hncov⟩ | ⟨p, hp, q, hq, -, hpqround, hpqkey⟩
    · simp only [readyView, Finset.mem_image] at hx
      obtain ⟨z, hz, hzx⟩ := hx
      rw [← hzx] at hncov hdom
      have hzraw := (Finset.mem_filter.mp hz).1
      by_cases hzs : s ≤ z.round
      · exact absurd (rawInputs_localCovers S rho sch auth roots hR b0 s (s + 1) Pn hconf
          hhead hfirst hexec.boundaryPublic w hw hFP u huh (late S.E S.hc (s + 1) .g2)
          hzraw hzs) hncov
      · push_neg at hzs
        obtain ⟨a, hav, har, hap, hwin, halt, haem⟩ :=
          rawInputs_trace S rho sch auth (domain S.E S.hc (s + 1) .g2)
            (late S.E S.hc (s + 1) .g2) w S.hc.η_SG (s + 1) u huh hzraw
        have hvote : u ∈ honestRoundVoters S rho z.round :=
          (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u z.round).mpr
            ⟨huh, a, hav, har, har ▸ haem⟩
        have hnot : u ∉ honestRoundVoters S rho (s + 1 - 1) := by
          simp only [Nat.add_sub_cancel]
          intro hv1
          obtain ⟨c, hcround, hcinterp⟩ :=
            stage2_voter_early_input S rho b0 b1 s Pn hexec hmargin hhead w hw hFP u hv1
          have hle : c.round ≤ z.round :=
            hdom _ (Finset.mem_image_of_mem DecoupledConsensusModel.Protocol.token hcinterp)
          exact absurd (hcround ▸ hle) (Nat.not_le.mpr hzs)
        exact Proofs.NamedOutageInputs.stale_of_eligible_vote S rho hwin hvote hnot
    · simp only [rawView, Finset.mem_image] at hp hq
      obtain ⟨p', hp', hpx⟩ := hp
      obtain ⟨q', hq', hqx⟩ := hq
      rw [← hpx, ← hqx] at hpqround hpqkey
      obtain ⟨pa, _, hpr, hpproj, _, _, hpem⟩ :=
        rawInputs_trace S rho sch auth (domain S.E S.hc (s + 1) .g2)
          (late S.E S.hc (s + 1) .g2) w S.hc.η_SG (s + 1) u huh hp'
      obtain ⟨qa, _, hqr, hqproj, _, _, hqem⟩ :=
        rawInputs_trace S rho sch auth (domain S.E S.hc (s + 1) .g2)
          (late S.E S.hc (s + 1) .g2) w S.hc.η_SG (s + 1) u huh hq'
      have hpq : pa = qa := NamedOutageProvenance.emitted_same_round_unique S rho sch hpem hqem
        (by rw [hpr, hqr]; exact hpqround)
      exact absurd (show p'.confirmed = q'.confirmed by rw [← hpproj, ← hqproj, hpq]) hpqkey
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, huh⟩)

/-- **The `gradeBool` margin at the formation round**, from the two inclusions
and `GradeFormingMajority` at round `s + 1`, whose pairing round is exactly the
stable round `s`. -/
private theorem stage2_grade_formation (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (s : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hforming : GradeFormingThroughout S rho)
    (hconf : HonestConfirmedAtOrAbove S rho b0 s Pn.erase)
    (hhead : HonestHeadHeldAbove S rho b0 s Pn.erase)
    (w : V) (hw : w ∈ rho.honest)
    (hFP : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc (s + 1) .g2) w).st.core.F Pn.erase) :
    gradeBool S.E
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc (s + 1) .g2) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc (s + 1) .g2) w).st.core.F
      S.hc.η_SG (s + 1) (early S.E S.hc (s + 1) .g2) (late S.E S.hc (s + 1) .g2)
      Pn.erase = true := by
  have hcov : RoundCovered S rho (s + 1) :=
    Or.inl ⟨Proofs.HealingLemmas.a_nonneg S (s + 1),
      (stage2_a_succ_le S s b0 hmargin).trans (hexec.interval.2.1.trans hexec.interval.2.2)⟩
  have hmaj : S.E.electorate.weightOf ((Finset.univ \ rho.honest) ∪
      staleHistoricalVoters S rho (s + 1)) <
      S.E.electorate.weightOf (honestRoundVoters S rho s) :=
    hforming (s + 1) (Nat.succ_pos s) hcov
  have h1 := S.E.electorate.weightOf_mono
    (stage2_opposition_stale S rho b0 b1 s Pn hexec hmargin hconf hhead w hw hFP)
  have h2 := S.E.electorate.weightOf_mono
    (stage2_voters_positive S rho b0 b1 s Pn hexec hmargin hconf hhead w hw hFP)
  simp only [gradeBool, decide_eq_true_eq]
  omega

/-- **The formation row of the pre-boundary frame clause.** Every honest reader's opening read of
round `s + 1` either has the protected prefix at or below its finalized block,
or carries a round-`(s+1)` grade-2 frame result covering it.

`hslash` and `hbudget` are NOT used: the certificate route needed the budget for
the retention window of the inventory time, and the inventory time is gone; the
slashable bound entered only through L4, which this row does not call — the
finality guard at a PRE-boundary read (`finalized_le_before_boundary`) and the
pre-boundary holding (`NamedEarlyHolding.stable_prefix_held_before_boundary`)
replace it. -/
theorem stage2_formation_g2 (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (v : V) (s : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hsleep : OutageSleepyThroughout S rho) (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hseed : OutputSeed S rho b0 s Pn.erase)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hconf1 : HonestConfirmedAtOrAbove S rho b0 s Pn.erase)
    (hconf2 : HonestHeadHeldAbove S rho b0 s Pn.erase) :
    ∀ w ∈ rho.honest,
      let n := NamedRun.readAt S rho (domain S.E S.hc (s + 1) .g1) w
      Block.Preceq Pn.erase n.st.core.F ∨
        ∃ raw : Block V,
          (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing (s + 1)).g2 =
            some (some raw) ∧ Block.Preceq Pn.erase raw := by
  obtain ⟨Pm, hPe, hscope, _⟩ := NamedBoundaryHolding.stable_prefix_held_at_boundary
    S rho b0 b1 hexec hsleep v hv s Pn.erase hmargin hseed hno
  rw [← hPe] at hseed hno hconf1 hconf2
  intro w hw
  show Block.Preceq Pn.erase
      (NamedRun.readAt S rho (domain S.E S.hc (s + 1) .g1) w).st.core.F ∨
    ∃ raw : Block V,
      (DecoupledConsensusModel.Protocol.readFrame
        (NamedRun.readAt S rho (domain S.E S.hc (s + 1) .g1) w).cache
        (NamedRun.readAt S rho (domain S.E S.hc (s + 1) .g1) w).st.core.toHealing (s + 1)).g2 =
          some (some raw) ∧ Block.Preceq Pn.erase raw
  rw [← hPe]
  have hR : 3 ≤ S.hc.R := S.hc.R_ge_three
  have hasucc : S.a (s + 1) ≤ b0 := stage2_a_succ_le S s b0 hmargin
  have hg2b0 : domain S.E S.hc (s + 1) .g2 ≤ b0 :=
    ((domain_le_opening S (s + 1)).trans (incl_opening_le_a S (s + 1))).trans hasucc
  have hcut1 : domain S.E S.hc (s + 1) .g1 + 1 ≤ b0 :=
    (stage2_opening_cut_le_a S (s + 1)).trans hasucc
  have hg2hor : domain S.E S.hc (s + 1) .g2 ≤ rho.horizon :=
    hg2b0.trans (hexec.interval.2.1.trans hexec.interval.2.2)
  have hbridge : NamedRun.readAt S rho (domain S.E S.hc (s + 1) .g1) w =
      NamedRun.stateBeforeTime S rho (domain S.E S.hc (s + 1) .g1 + 1) w := by
    rw [incl_readAt_eq_succ]
  by_cases hneed : NeedsSG S rho Pm (s + 1) w
  · right
    have hFPdom : Block.Preceq
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc (s + 1) .g2) w).st.core.F Pm.erase :=
      finalized_le_before_boundary S rho b0 b1 s (s + 1) Pm hexec hmargin hsleep hscope hno
        w hw hneed (domain S.E S.hc (s + 1) .g2) hg2b0 (incl_g2_le_opening_cut S (s + 1))
    have hdead : S.a s + S.E.Δ ≤ domain S.E S.hc (s + 1) .g2 :=
      (action_delta_le_early S hR (Nat.lt_succ_self s)).trans (early_le_domain S (s + 1))
    obtain ⟨Pk, hPke, _, hPkheld⟩ := NamedEarlyHolding.stable_prefix_held_before_boundary_of_seed
      S rho b0 b1 hexec hsleep v hv s Pm.erase hmargin hseed hno
      (domain S.E S.hc (s + 1) .g2) hdead hg2b0
    have hmemT : Pm.erase ∈
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc (s + 1) .g2) w).st.core.T := by
      have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
        (domain S.E S.hc (s + 1) .g2) w).1.1.1
      rw [hcoh.1, ← hPke]
      exact Finset.mem_image_of_mem _ (hPkheld w hw)
    obtain ⟨raw0, hfreeze, hPraw0⟩ := sg_freeze_of_graded S.E _ _ S.hc.η_SG (s + 1)
      (stage2_early_le_late S (s + 1)) hmemT
      (stage2_grade_formation S rho b0 b1 s Pm hexec hmargin hforming hconf1 hconf2 w hw hFPdom)
    have hcomp := FrameCompleted.frame_g2_completed S rho hexec.core w hw (s + 1)
      (Nat.succ_pos s) (domain S.E S.hc (s + 1) .g1 + 1) (stage2_g2_lt_opening_cut S (s + 1))
      (stage2_opening_cut_le_a S (s + 1)) hg2hor
    rw [hfreeze] at hcomp
    rw [← hbridge] at hcomp
    simp only [Option.map_some] at hcomp
    have hF' : Block.compatible Pm.erase
        (NamedRun.readAt S rho (domain S.E S.hc (s + 1) .g1) w).st.core.F = true := by
      rw [hbridge]
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr (finalized_le_before_boundary S rho b0 b1 s (s + 1) Pm hexec hmargin hsleep
        hscope hno w hw hneed (domain S.E S.hc (s + 1) .g1 + 1) hcut1 le_rfl)
    exact ⟨_, hcomp, clip_retains _ _ _ hF' hPraw0⟩
  · exact Or.inl (not_not.mp hneed)

#print axioms stage2_formation_g2

/-- **The pre-boundary frame clause, whole.** `Nat` trichotomy against
`s + 1 ≤ q`: above the stable round's successor it is
`stage2_preBoundaryFrames_above`, and at the formation
row `q = s + 1` it is `stage2_formation_g2`. -/
theorem stage2_preBoundaryFrames (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (v : V) (s : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hsleep : OutageSleepyThroughout S rho) (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hseed : OutputSeed S rho b0 s Pn.erase)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hconf1 : HonestConfirmedAtOrAbove S rho b0 s Pn.erase)
    (hconf2 : HonestHeadHeldAbove S rho b0 s Pn.erase)
    (hbudget : StableRetentionBudget S rho v s Pn.erase b1) :
    PreBoundaryFrames S rho b0 s Pn.erase := by
  intro w hw q hq hqb0
  rcases Nat.lt_or_ge (s + 1) q with hgap | hle
  · exact stage2_preBoundaryFrames_above S rho b0 b1 v s Pn hexec hslash hsleep hforming hv
      hmargin hseed hno hconf1 hconf2 hbudget w hw q hgap hqb0
  · have hq1 : q = s + 1 := Nat.le_antisymm hle hq
    subst hq1
    exact stage2_formation_g2 S rho b0 b1 v s Pn hexec hsleep hforming hv hmargin hseed hno
      hconf1 hconf2 w hw

#print axioms stage2_preBoundaryFrames







/-! The lower bound of the query at the formation read. `omega` refuses a goal
stated at the `Time`/`Round`/`Slot` aliases and cannot see `Δ_pos`, so the
arithmetic core is stated over raw `Int` and applied. -/









end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
