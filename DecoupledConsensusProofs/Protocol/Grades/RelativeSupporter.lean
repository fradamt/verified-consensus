module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.Q20_graded_has_honest_supporter
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionHistory
public import DecoupledConsensusProofs.Generic.EvaluationStore
public import DecoupledConsensusProofs.Generic.GSTZeroHealthy
public import DecoupledConsensusProofs.Protocol.Grades.HealthyHeadReady
public import DecoupledConsensusProofs.Protocol.Grades.Inclusions
public import DecoupledConsensusProofs.Protocol.Grades.Persistence

@[expose] public section

/-!
# Relative-grade supporter producer

The relative grade compares the weight of opposing validators with the weight
of positive validators. Its honest-supporter extraction therefore uses the
reader-level `WindowMajorityAt` premise. The pure proof below is the relative
counterpart of the direct-support extraction in `Proofs.HealingLemmas.Grades`.

The run-level raw representation facts are kept separate. They prove
`Protocol.represented`, while `WindowMajorityAt` counts `honestPresent`,
which requires an `interpretedInputs` witness and therefore body open.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Interpreted participation implies the window majority -/

/- The arithmetic implication is independent of the delivery proof. The
  run-level producer must supply an interpreted input, not only a raw
  `Protocol.represented` vote. -/
theorem windowMajorityAt_of_honestWeightMajority_of_interpreted
    (S : Setup V)
    {gv : Protocol.GradeView V} {F : Block V} {Hon : Finset V}
    {r : Round} {cutoff : Time}
    (hmajority : HonestWeightMajority S Hon)
    (hinterpreted : ∀ v ∈ Hon,
      (interpretedInputs gv F S.hc.η_SG r cutoff v).Nonempty) :
    WindowMajorityAt S.E S.hc gv F Hon r cutoff := by
  unfold WindowMajorityAt
  have hsubset : Hon ⊆ honestPresent S.hc gv F Hon r cutoff := by
    intro v hv
    simp only [honestPresent, Finset.mem_filter]
    exact ⟨hv, hinterpreted v hv⟩
  exact lt_of_lt_of_le (by simpa only [HonestWeightMajority] using hmajority)
    (S.E.electorate.weightOf_mono hsubset)

/-! ## GST-zero interpreted participation -/


/-- The run-level majority wrapper keeps the raw representation premise beside
the interpreted-input producer. The weight calculation itself uses the latter
because `WindowMajorityAt` counts interpreted inputs. -/
theorem windowMajorityAt_of_honestWeightMajority_of_represented
    (S : Setup V)
    {gv : Protocol.GradeView V} {F : Block V} {Hon : Finset V}
    {r : Round} {cutoff : Time}
    (hmajority : HonestWeightMajority S Hon)
    (hrepresented : ∀ v ∈ Hon,
      Protocol.represented gv.sg_votes S.hc.η_SG v r = true)
    (hinterpreted : ∀ v ∈ Hon,
      (interpretedInputs gv F S.hc.η_SG r cutoff v).Nonempty) :
    WindowMajorityAt S.E S.hc gv F Hon r cutoff := by
  apply windowMajorityAt_of_honestWeightMajority_of_interpreted S hmajority
  intro v hv
  have hraw := hrepresented v hv
  simpa only [hraw] using hinterpreted v hv

/-! ## Relative positive-support extraction -/

private theorem honest_positive_of_windowMajority
    (E : Env V) (hc : Protocol.HealConfig)
    {gv : Protocol.GradeView V} {F : Block V} {Hon : Finset V}
    {r : Round} {B : Block V} {p : Phase}
    (hwindow : WindowMajorityAt E hc gv F Hon r (early E hc r p))
    (hgrade : gradeBool E gv F hc.η_SG r (early E hc r p)
      (late E hc r p) B = true) :
    ∃ v ∈ Hon,
      positive gv F hc.η_SG r (early E hc r p) (late E hc r p) v B = true := by
  by_contra hno
  push Not at hno
  have hnopos : ∀ v ∈ Hon,
      positive gv F hc.η_SG r (early E hc r p) (late E hc r p) v B ≠ true := by
    intro v hv
    exact hno v hv
  have hopp : honestPresent hc gv F Hon r (early E hc r p) ⊆
      Finset.univ.filter fun v =>
        opposing gv F hc.η_SG r (early E hc r p) (late E hc r p) v B = true := by
    intro v hv
    simp only [honestPresent, Finset.mem_filter] at hv
    obtain ⟨hvH, hvne⟩ := hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, opposing,
      decide_eq_true_eq]
    rcases Proofs.HealingLemmas.Rows.supports_or_opposes
        (fun k b => localCovers gv k b = true)
        (readyView gv F hc.η_SG r (early E hc r p) v)
        (readyView gv F hc.η_SG r (late E hc r p) v)
        (rawView gv hc.η_SG r (late E hc r p) v) B
        (hvne.image DecoupledConsensusModel.Protocol.token)
        (GradeCutoffMono.readyView_mono gv F hc.η_SG r
          (GradeCutoffMono.early_le_late E hc r p) v) with hs | ho
    · exact absurd
        (show positive gv F hc.η_SG r (early E hc r p) (late E hc r p) v B = true by
          simp only [positive, decide_eq_true_eq]
          exact hs)
        (hnopos v hvH)
    · exact ho
  have hposfaulty : Finset.univ.filter (fun v =>
      positive gv F hc.η_SG r (early E hc r p) (late E hc r p) v B = true) ⊆
      Finset.univ \ Hon := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact fun hvH => hnopos v hvH hv
  simp only [gradeBool, decide_eq_true_eq] at hgrade
  simp only [WindowMajorityAt] at hwindow
  have h1 : E.electorate.weightOf (Finset.univ \ Hon) <
      E.electorate.weightOf (Finset.univ.filter fun v =>
        opposing gv F hc.η_SG r (early E hc r p) (late E hc r p) v B = true) :=
    lt_of_lt_of_le hwindow (E.electorate.weightOf_mono hopp)
  have h2 : E.electorate.weightOf (Finset.univ.filter fun v =>
      positive gv F hc.η_SG r (early E hc r p) (late E hc r p) v B = true) ≤
      E.electorate.weightOf (Finset.univ \ Hon) :=
    E.electorate.weightOf_mono hposfaulty
  exact absurd (lt_of_lt_of_le (lt_trans h1 hgrade) h2) (lt_irrefl _)

/-- A relative grade has an honest positive supporter under the reader's
window-majority bound. The supporter carries an interpreted input whose
resolved head covers the graded block. -/
theorem exists_honest_positive_supporter_of_relativeGrade
    (E : Env V) (hc : Protocol.HealConfig)
    {gv : Protocol.GradeView V} {F : Block V} {Hon : Finset V}
    {r : Round} {B : Block V} {p : Phase}
    (hwindow : WindowMajorityAt E hc gv F Hon r (early E hc r p))
    (hgrade : gradeBool E gv F hc.η_SG r (early E hc r p)
      (late E hc r p) B = true) :
    ∃ v ∈ Hon,
      ∃ u ∈ interpretedInputs gv F hc.η_SG r (early E hc r p) v,
        ∃ head : Block V, u.confirmed = some head.root ∧
          Block.find? gv.T head.root = some head ∧ head ∈ gv.T ∧
          Block.Preceq B head ∧
          positive gv F hc.η_SG r (early E hc r p) (late E hc r p) v B = true := by
  obtain ⟨v, hv, hpositive⟩ :=
    honest_positive_of_windowMajority E hc hwindow hgrade
  have hsupport : Supports (fun k b => localCovers gv k b = true)
      (readyView gv F hc.η_SG r (early E hc r p) v)
      (readyView gv F hc.η_SG r (late E hc r p) v)
      (rawView gv hc.η_SG r (late E hc r p) v) B := by
    simpa only [positive, decide_eq_true_eq] using hpositive
  have hsupport' := hsupport
  obtain ⟨tok, htok, -, hcov, -, -⟩ := hsupport'
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp htok
  simp only [localCovers, DecoupledConsensusModel.Protocol.token] at hcov
  obtain ⟨root, head, hroot, hfind, hmem, hpre⟩ :=
    Proofs.HealingLemmas.exists_head_of_head_covers hcov
  have hheadroot : head.root = root := Proofs.HealingLemmas.find?_root hfind
  refine ⟨v, hv, u, hu, head, ?_, ?_, hmem, hpre, ?_⟩
  · rw [hheadroot]
    exact hroot
  · rw [hheadroot]
    exact hfind
  · simp only [positive, decide_eq_true_eq]
    exact hsupport

/-- The selected honest positive supporter is maximal in the early
interpreted view. This retains the ordering field of `Supports` for consumers
that identify the supporter with the latest honest action vote. -/
theorem exists_honest_max_positive_supporter_of_relativeGrade
    (E : Env V) (hc : Protocol.HealConfig)
    {gv : Protocol.GradeView V} {F : Block V} {Hon : Finset V}
    {r : Round} {B : Block V} {p : Phase}
    (hwindow : WindowMajorityAt E hc gv F Hon r (early E hc r p))
    (hgrade : gradeBool E gv F hc.η_SG r (early E hc r p)
      (late E hc r p) B = true) :
    ∃ v ∈ Hon,
      ∃ u ∈ interpretedInputs gv F hc.η_SG r (early E hc r p) v,
        ∃ head : Block V, u.confirmed = some head.root ∧
          Block.find? gv.T head.root = some head ∧ head ∈ gv.T ∧
          Block.Preceq B head ∧
          positive gv F hc.η_SG r (early E hc r p)
            (late E hc r p) v B = true ∧
          ∀ x ∈ interpretedInputs gv F hc.η_SG r (early E hc r p) v,
            x.round ≤ u.round := by
  obtain ⟨v, hv, hpositive⟩ :=
    honest_positive_of_windowMajority E hc hwindow hgrade
  have hsupport : Supports (fun k b => localCovers gv k b = true)
      (readyView gv F hc.η_SG r (early E hc r p) v)
      (readyView gv F hc.η_SG r (late E hc r p) v)
      (rawView gv hc.η_SG r (late E hc r p) v) B := by
    simpa only [positive, decide_eq_true_eq] using hpositive
  obtain ⟨tok, htok, hmax, hcov, -, -⟩ := hsupport
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp htok
  simp only [localCovers, DecoupledConsensusModel.Protocol.token] at hcov
  obtain ⟨root, head, hroot, hfind, hmem, hpre⟩ :=
    Proofs.HealingLemmas.exists_head_of_head_covers hcov
  have hheadroot : head.root = root := Proofs.HealingLemmas.find?_root hfind
  refine ⟨v, hv, u, hu, head, ?_, ?_, hmem, hpre, hpositive, ?_⟩
  · rw [hheadroot]
    exact hroot
  · rw [hheadroot]
    exact hfind
  · intro x hx
    exact hmax (DecoupledConsensusModel.Protocol.token x)
      (Finset.mem_image_of_mem DecoupledConsensusModel.Protocol.token hx)




omit [Fintype V] in
private theorem named_ancestor_body_mem_local
    {st : Protocol.NamedStore V} (hpc : NamedStore.NamedParentClosed st)
    {A B : NamedBlock V} (hB : B ∈ st.bodies)
    (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
      exact hAB ▸ hB
  | node parent slot root votes support rows proposer ih =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · exact ih (hpc.2 _ hB) hparent

private theorem held_find_at_strict_local
    (S : Setup V) {rho : Run V}
    (sch : NamedScheduleWellFormed S rho)
    (roots : NamedRootCollisionFree S rho) (reader : V)
    (hreader : reader ∈ rho.honest) (t : Time) (H : NamedBlock V)
    (hH : H ∈ (NamedRun.stateBeforeTime S rho t reader).st.bodies) :
    Block.find?
        (NamedRun.stateBeforeTime S rho t reader).st.core.T H.erase.root =
      some H.erase := by
  obtain ⟨n, hread, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sch.sorted t
  rw [hread] at hH ⊢
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho n reader).1.1.1
  have hHscope := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hreader n hH)
  have hHraw : H.erase ∈ (NamedRun.stateBefore S rho n reader).st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hH
  apply Proofs.Optimistic.find?_eq_some_of_unique hHraw
  intro raw hraw hroot
  rw [hcoh.1] at hraw
  obtain ⟨other, hother, rfl⟩ := Finset.mem_image.mp hraw
  have hotherScope := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hreader n hother)
  have hroots : other.root = H.root :=
    (Proofs.NamedWire.erase_root other).symm.trans (hroot.trans (Proofs.NamedWire.erase_root H))
  have heq := roots.root_injective other H hotherScope hHscope other H
    (Or.inl (Proofs.NamedAncestry.named_self other))
    (Or.inr (Proofs.NamedAncestry.named_self H)) hroots
  exact congrArg NamedBlock.erase heq





/-- A post-GST honest window vote is interpretable when its named head and the
reader's finalized root have one common upper block. This is the directed
finalized-prefix transport used by the ceiling proof, with the reverse
orientation handled by ancestor retention. -/
theorem action_vote_mem_interpretedInputs_after_gst_common_upper
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {t : Time} {r k : Round} (p : Phase)
    (hk : k ∈ Protocol.latest_window S.hc.η_SG r)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {a : NamedAttestation V} {H : NamedBlock V} {C : Block V}
    (hvote : a.val_index = v ∧ a.round = k ∧
      NamedRun.emits S rho v (Object.attest a) (S.a k))
    (hhead : ∃ i : Nat, rho.events[i]? = some (.tick v (S.a k)) ∧
      H ∈ (NamedActionReads.actionReadFrom S
        (NamedRun.stateBefore S rho i v) a.round).st.bodies ∧
      a.confirmed = some H.root)
    (hHC : Block.Preceq H.erase C)
    (hFC : Block.Preceq
      (NamedRun.stateBeforeTime S rho t w).st.core.F C)
    (hpost : S.E.t_GST ≤ S.a a.round)
    (hdeadline : max (S.a a.round) S.E.t_GST + S.E.Δ ≤
      early S.E S.hc r p)
    (horder : early S.E S.hc r p ≤ t)
    (hcut : early S.E S.hc r p ≤ rho.horizon) :
    Protocol.sgVote a.erase ∈ interpretedInputs
      (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho t w).st.core.F
      S.hc.η_SG r (early S.E S.hc r p) v := by
  obtain ⟨i, hi, hH, hconfirmed⟩ := hhead
  have hval : a.val_index ∈ rho.honest := by
    simpa only [hvote.1] using hv
  have hi' : rho.events[i]? = some (.tick v (S.a a.round)) := by
    simpa only [hvote.2.1] using hi
  have hbody : H ∈ (NamedRun.stateBefore S rho i v).st.bodies := by
    change H ∈ (NamedRun.stateBefore S rho i v).st.bodies at hH
    exact hH
  have hstate := NamedActionSources.action_read_index S rho
    core.toNamedScheduleWellFormed i v a.round hi'
  have hHsource : H ∈
      (NamedRun.stateBeforeTime S rho (S.a a.round) v).st.bodies := by
    rw [← hstate]
    exact hbody
  have hFmono : Block.Preceq
      (NamedRun.stateBeforeTime S rho (early S.E S.hc r p) w).st.core.F
      (NamedRun.stateBeforeTime S rho t w).st.core.F := by
    rw [NamedOutageClosure.strict_read_eq_index S rho
      core.toNamedScheduleWellFormed.sorted (early S.E S.hc r p),
      NamedOutageClosure.strict_read_eq_index S rho
        core.toNamedScheduleWellFormed.sorted t]
    exact Proofs.NamedRuntime.stateBefore_F_mono S rho w
      (NamedOutageClosure.strict_lengths_mono rho horder)
  have hcompFD : Block.compatible H.erase
      (NamedRun.stateBeforeTime S rho t w).st.core.F = true :=
    Block.compatible_of_preceq_common hHC hFC
  have hcompFE : Block.compatible H.erase
      (NamedRun.stateBeforeTime S rho (early S.E S.hc r p) w).st.core.F = true := by
    have hcompFD' : H.erase.preceq
          (NamedRun.stateBeforeTime S rho t w).st.core.F = true ∨
        (NamedRun.stateBeforeTime S rho t w).st.core.F.preceq H.erase = true := by
      simpa only [Block.compatible, Bool.or_eq_true] using hcompFD
    rcases hcompFD' with hHF | hFH
    · exact Block.compatible_of_preceq_common hHF hFmono
    · simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr (Block.preceq_trans hFmono hFH)
  have hready : H ∈
      (NamedRun.stateBeforeTime S rho t w).st.bodies ∧
      stampedBefore
        (NamedRun.stateBeforeTime S rho t w).st.core.timestamp_block
        (early S.E S.hc r p) H.erase = true ∧
      Block.find?
        (NamedRun.stateBeforeTime S rho t w).st.core.T H.root = some H.erase := by
    have hcompFE' := hcompFE
    simp only [Block.compatible, Bool.or_eq_true] at hcompFE'
    rcases hcompFE' with hHF | hFH
    · have hFmem := Proofs.NamedStoreBridge.finalizedInTree_stateBeforeTime S rho
          (early S.E S.hc r p) w
      obtain ⟨Fname, hFname, hFerase⟩ :=
        Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
          (early S.E S.hc r p) w hFmem
      have hFnameTime := hFname
      have hHFn : H.erase ⪯ Fname.erase := by
        rw [hFerase]
        exact hHF
      obtain ⟨A, hAF, hAerase⟩ := Proofs.NamedAncestry.erased_ancestor_lift Fname hHFn
      obtain ⟨n, hread, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
        core.toNamedScheduleWellFormed.sorted (early S.E S.hc r p)
      change Fname ∈
        (NamedRun.stateBeforeTime S rho (early S.E S.hc r p) w).st.bodies at hFname
      rw [hread] at hFname
      have hFnameRun := Proofs.NamedRuntime.blockInRun_of_direct S rho
        (Proofs.NamedRuntime.directBlock_of_prefix S rho hw n hFname)
      have hArun := Proofs.NamedRuntime.blockInRun_of_ancestor S rho hFnameRun hAF
      have hHrun := Proofs.NamedRuntime.blockInRun_of_direct S rho
        (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hbody)
      have hAroot : A.root = H.root := by
        have : A.erase.root = H.root := by
          rw [hAerase, Proofs.NamedWire.erase_root]
        simpa only [Proofs.NamedWire.erase_root] using this
      have hAH := core.toNamedRootCollisionFree.root_injective A H hArun hHrun
        A H (Or.inl (Proofs.NamedAncestry.named_self A))
        (Or.inr (Proofs.NamedAncestry.named_self H)) hAroot
      have hAheld : A ∈
          (NamedRun.stateBeforeTime S rho
            (early S.E S.hc r p) w).st.bodies :=
        named_ancestor_body_mem_local
          ((Proofs.NamedRuntime.stateBeforeTime_invariants S rho
            (early S.E S.hc r p) w).1.1.1.2.2.1) hFnameTime hAF
      have hHheld : H ∈
          (NamedRun.stateBeforeTime S rho
            (early S.E S.hc r p) w).st.bodies := by
        rw [← hAH]
        exact hAheld
      have hstampE :=
        NamedBlockStamp.held_body_stampedBefore_stateBeforeTime S rho
          core.toNamedScheduleWellFormed w (early S.E S.hc r p) H hHheld
      obtain ⟨hheld, hstampCarry⟩ :=
        NamedOutageClosure.q10_strict_body_carry S rho
          core.toNamedScheduleWellFormed w horder hHheld
      have hstamp : stampedBefore
          (NamedRun.stateBeforeTime S rho t w).st.core.timestamp_block
          (early S.E S.hc r p) H.erase = true := by
        unfold stampedBefore at hstampE ⊢
        rw [hstampCarry]
        exact hstampE
      have hfind := held_find_at_strict_local S core.toNamedScheduleWellFormed
        core.toNamedRootCollisionFree w hw t H hheld
      rw [Proofs.NamedWire.erase_root H] at hfind
      exact ⟨hheld, hstamp, hfind⟩
    · obtain ⟨hheldE, hstampE, -⟩ :=
        NamedHealthyHeadReady.healthy_head_body_at_read_after_gst S rho core
          v hv w hw H (S.a a.round) (early S.E S.hc r p)
          (early S.E S.hc r p) hHsource hdeadline le_rfl hcut hFH
      obtain ⟨hheld, hstampCarry⟩ :=
        NamedOutageClosure.q10_strict_body_carry S rho
          core.toNamedScheduleWellFormed w horder hheldE
      have hstamp : stampedBefore
          (NamedRun.stateBeforeTime S rho t w).st.core.timestamp_block
          (early S.E S.hc r p) H.erase = true := by
        unfold stampedBefore at hstampE ⊢
        rw [hstampCarry]
        exact hstampE
      have hfind := held_find_at_strict_local S core.toNamedScheduleWellFormed
        core.toNamedRootCollisionFree w hw t H hheld
      rw [Proofs.NamedWire.erase_root H] at hfind
      exact ⟨hheld, hstamp, hfind⟩
  obtain ⟨hheld, hstamp, hfind⟩ := hready
  have hem : NamedRun.emits S rho a.val_index (Object.attest a)
      (S.a a.round) := by
    simpa only [hvote.1, hvote.2.1] using hvote.2.2
  have hactionDeadline : S.a a.round + S.E.Δ ≤ early S.E S.hc r p :=
    (Int.add_le_add_right
      (le_max_left (S.a a.round) S.E.t_GST) S.E.Δ).trans hdeadline
  let healthy := NamedOutageClosure.healthyWindowDelivery_after_gst S rho core
  obtain ⟨td, hlo, hhi, j, hcall⟩ := healthy.broadcast a.val_index hval
    (Object.attest a) (S.a a.round) hem w hw hpost
    (hactionDeadline.trans hcut) rfl
  have hrow := Proofs.NamedSGArrival.honest_row_after_call S rho
    core.toNamedScheduleWellFormed core.toNamedUnforgeable hval hem hcall hlo hhi
  obtain ⟨e, he, _, het⟩ := hcall.2
  obtain ⟨_, stamp, hstampBound, hstampEvent⟩ :=
    Proofs.NamedSGArrival.held_row_own_and_stamp_at_event S rho
      core.toNamedScheduleWellFormed he w a.round a hrow
  have htdEarly : td < early S.E S.hc r p := hhi.trans_le hactionDeadline
  have heEarly : e.time < early S.E S.hc r p := by
    simpa only [het] using htdEarly
  have heCut : e.time < t := heEarly.trans_le horder
  let cut := t
  let n := (rho.events.filter (fun e => decide (e.time < cut))).length
  have hread : NamedRun.stateBeforeTime S rho cut =
      NamedRun.stateBefore S rho n :=
    Proofs.Optimistic.stateBeforeTime_eq_take S core.toNamedScheduleWellFormed cut
  have hjN : j < n := by
    by_contra hnot
    have hnj : n ≤ j := Nat.le_of_not_gt hnot
    have hle := Proofs.Optimistic.le_time_of_index_ge S
      core.toNamedScheduleWellFormed (t := cut) (j := j) (e := e) hnj he
    exact (not_le_of_gt heCut) hle
  have hrowN := Proofs.NamedSGArrival.stateBefore_sg_row_stamp_mono S rho w
    (Nat.succ_le_of_lt hjN) hrow
  have hrowCut : a ∈
      (NamedRun.stateBeforeTime S rho t w).st.sg_rows a.round := by
    rw [hread]
    exact hrowN.1
  have hstampCut :
      (NamedRun.stateBeforeTime S rho t w).st.core.timestamp_sg_vote
        (Protocol.sgVote a.erase) = some (stamp : Stamp) := by
    rw [hread]
    exact hrowN.2.trans hstampEvent
  have hstampEarly : stamp < early S.E S.hc r p := hstampBound.trans_lt heEarly
  have hoccur : occurrenceBefore
      ((NamedRun.stateBeforeTime S rho t w).st.core.timestamp_sg_vote
        (Protocol.sgVote a.erase)) (early S.E S.hc r p) = true := by
    simp only [hstampCut, occurrenceBefore, decide_eq_true_eq]
    exact WithBot.coe_lt_coe.mpr hstampEarly
  have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t w).1.1.1
  have hpool := NamedAdmission.pool_view_mem _ hcoh.2.2.2.1 a hrowCut
  let target := NamedRun.stateBeforeTime S rho t w
  have hsg : Protocol.sgVote a.erase ∈
      target.st.core.toHealing.gradeView.sg_votes a.round :=
    Finset.mem_image_of_mem Protocol.sgVote hpool
  have hraw : Protocol.sgVote a.erase ∈
      rawInputs target.st.core.toHealing.gradeView S.hc.η_SG r
        (early S.E S.hc r p) v := by
    simp only [rawInputs, Finset.mem_filter]
    refine ⟨Finset.mem_biUnion.mpr ?_, ?_, hoccur⟩
    · exact ⟨a.round, List.mem_toFinset.mpr (by
        simpa only [hvote.2.1] using hk), hsg⟩
    · rw [NamedOutageClosure.sgVote_val, hvote.1]
  have hconf : (Protocol.sgVote a.erase).confirmed = some H.root := by
    rw [NamedOutageClosure.sgVote_confirmed, hconfirmed]
  have hfind' : Block.find? target.st.core.T H.root = some H.erase := by
    simpa only [target, Proofs.NamedWire.erase_root] using hfind
  have hbodyReady : bodyReady target.st.core.toHealing.gradeView target.st.core.F
      (early S.E S.hc r p) (Protocol.sgVote a.erase) = true := by
    simp only [bodyReady, hconf]
    change (match Block.find? target.st.core.T H.root with
      | none => false
      | some head => stampedBefore target.st.core.timestamp_block
          (early S.E S.hc r p) head &&
          Block.compatible head target.st.core.F) = true
    rw [hfind', Bool.and_eq_true]
    exact ⟨hstamp, by simpa only [target] using hcompFD⟩
  exact Finset.mem_filter.mpr ⟨hraw, hbodyReady⟩


/-- Exact-token form of the post-GST common-upper transport. The named root
collision rule identifies the body selected by the target store with the
named head carried by the source action. -/
theorem interpretedInputs_exact_of_honest_window_vote_after_gst_common_upper
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {t : Time} {r k : Round} (p : Phase)
    (hk : k ∈ Protocol.latest_window S.hc.η_SG r)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {a : NamedAttestation V} {H : NamedBlock V} {C : Block V}
    (hvote : a.val_index = v ∧ a.round = k ∧
      NamedRun.emits S rho v (Object.attest a) (S.a k))
    (hhead : ∃ i : Nat, rho.events[i]? = some (.tick v (S.a k)) ∧
      H ∈ (NamedActionReads.actionReadFrom S
        (NamedRun.stateBefore S rho i v) a.round).st.bodies ∧
      a.confirmed = some H.root)
    (hHC : Block.Preceq H.erase C)
    (hFC : Block.Preceq
      (NamedRun.stateBeforeTime S rho t w).st.core.F C)
    (hpost : S.E.t_GST ≤ S.a a.round)
    (hdeadline : max (S.a a.round) S.E.t_GST + S.E.Δ ≤
      early S.E S.hc r p)
    (horder : early S.E S.hc r p ≤ t)
    (hcut : early S.E S.hc r p ≤ rho.horizon) :
    ∃ y ∈ interpretedInputs
      (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho t w).st.core.F
      S.hc.η_SG r (early S.E S.hc r p) v,
      y.round = k ∧
      y.confirmed = some H.erase.root ∧
      Block.find?
        (NamedRun.stateBeforeTime S rho t w).st.core.T H.root = some H.erase := by
  have hmem := action_vote_mem_interpretedInputs_after_gst_common_upper
    S core p hk hv hw hvote hhead hHC hFC hpost hdeadline horder hcut
  obtain ⟨i, hi, hH, hconfirmed⟩ := hhead
  have hi' : rho.events[i]? = some (.tick v (S.a a.round)) := by
    simpa only [hvote.2.1] using hi
  have hHbody : H ∈ (NamedRun.stateBefore S rho i v).st.bodies := by
    change H ∈ (NamedRun.stateBefore S rho i v).st.bodies at hH
    exact hH
  have hHrun : RunBlock S rho H :=
    Proofs.NamedRuntime.blockInRun_of_direct S rho
      (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hHbody)
  have hready := (Finset.mem_filter.mp hmem).2
  have hvoteConfirmed : (Protocol.sgVote a.erase).confirmed = some H.root := by
    rw [NamedOutageClosure.sgVote_confirmed, hconfirmed]
  cases hfind : Block.find?
      (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.gradeView.T H.root with
  | none =>
      simp [DecoupledConsensusModel.Protocol.bodyReady, hvoteConfirmed, hfind] at hready
  | some X =>
      have hXmem : X ∈ (NamedRun.stateBeforeTime S rho t w).st.core.T :=
        by simpa only using Proofs.HealingLemmas.find?_mem hfind
      obtain ⟨Xn, hXerase, hXrun⟩ :=
        Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
          core.toNamedScheduleWellFormed hw t hXmem
      have hroot : Xn.root = H.root := by
        rw [← Proofs.NamedWire.erase_root Xn, hXerase]
        exact Proofs.HealingLemmas.find?_root hfind
      have hXH : Xn = H := core.toNamedRootCollisionFree.root_injective
        Xn H hXrun hHrun Xn H
          (Or.inl (Proofs.NamedAncestry.named_self Xn))
          (Or.inr (Proofs.NamedAncestry.named_self H)) hroot
      refine ⟨Protocol.sgVote a.erase, hmem, ?_, ?_, ?_⟩
      · simpa only [NamedOutageClosure.sgVote_round] using hvote.2.1
      · rw [NamedOutageClosure.sgVote_confirmed, hconfirmed,
          Proofs.NamedWire.erase_root]
      · exact hfind.trans (congrArg some
          (hXerase.symm.trans (congrArg NamedBlock.erase hXH)))

/-! ## Delivery-parametric common-upper transport -/

/-- A healthy-prefix delivery contract transports an honest window vote to any
later prepared read when the action body and the reader have a common upper
block. The cap is explicit so the same producer serves the post-GST and
pre-outage delivery instances. -/
private theorem action_vote_mem_interpretedInputs_of_delivery_common_upper
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {cap t : Time} {r k : Round} (p : Phase)
    (hdelivery : NamedHealthyPrefixDelivery S rho cap)
    (hk : k ∈ Protocol.latest_window S.hc.η_SG r)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {a : NamedAttestation V} {H : NamedBlock V} {C : Block V}
    (hvote : a.val_index = v ∧ a.round = k ∧
      NamedRun.emits S rho v (Object.attest a) (S.a k))
    (hhead : ∃ i : Nat, rho.events[i]? = some (.tick v (S.a k)) ∧
      H ∈ (NamedActionReads.actionReadFrom S
        (NamedRun.stateBefore S rho i v) a.round).st.bodies ∧
      a.confirmed = some H.root)
    (hHC : Block.Preceq H.erase C)
    (hFC : Block.Preceq
      (NamedRun.stateBeforeTime S rho t w).st.core.F C)
    (hdeadline : S.a a.round + S.E.Δ ≤
      early S.E S.hc r p)
    (horder : early S.E S.hc r p ≤ t)
    (hcut : early S.E S.hc r p ≤ cap) :
    Protocol.sgVote a.erase ∈ interpretedInputs
      (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho t w).st.core.F
      S.hc.η_SG r (early S.E S.hc r p) v ∧
      (Protocol.sgVote a.erase).round = k ∧
      (Protocol.sgVote a.erase).confirmed = some H.erase.root ∧
      Block.find?
        (NamedRun.stateBeforeTime S rho t w).st.core.T H.root = some H.erase := by
  obtain ⟨i, hi, hH, hconfirmed⟩ := hhead
  have hval : a.val_index ∈ rho.honest := by
    simpa only [hvote.1] using hv
  have hi' : rho.events[i]? = some (.tick v (S.a a.round)) := by
    simpa only [hvote.2.1] using hi
  have hbody : H ∈ (NamedRun.stateBefore S rho i v).st.bodies := by
    change H ∈ (NamedRun.stateBefore S rho i v).st.bodies at hH
    exact hH
  have hstate := NamedActionSources.action_read_index S rho
    core.toNamedScheduleWellFormed i v a.round hi'
  have hHsource : H ∈
      (NamedRun.stateBeforeTime S rho (S.a a.round) v).st.bodies := by
    rw [← hstate]
    exact hbody
  have hFmono : Block.Preceq
      (NamedRun.stateBeforeTime S rho (early S.E S.hc r p) w).st.core.F
      (NamedRun.stateBeforeTime S rho t w).st.core.F := by
    rw [NamedOutageClosure.strict_read_eq_index S rho
      core.toNamedScheduleWellFormed.sorted (early S.E S.hc r p),
      NamedOutageClosure.strict_read_eq_index S rho
        core.toNamedScheduleWellFormed.sorted t]
    exact Proofs.NamedRuntime.stateBefore_F_mono S rho w
      (NamedOutageClosure.strict_lengths_mono rho horder)
  have hcompFD : Block.compatible H.erase
      (NamedRun.stateBeforeTime S rho t w).st.core.F = true :=
    Block.compatible_of_preceq_common hHC hFC
  have hcompFE : Block.compatible H.erase
      (NamedRun.stateBeforeTime S rho (early S.E S.hc r p) w).st.core.F = true := by
    have hcompFD' : H.erase.preceq
          (NamedRun.stateBeforeTime S rho t w).st.core.F = true ∨
        (NamedRun.stateBeforeTime S rho t w).st.core.F.preceq H.erase = true := by
      simpa only [Block.compatible, Bool.or_eq_true] using hcompFD
    rcases hcompFD' with hHF | hFH
    · exact Block.compatible_of_preceq_common hHF hFmono
    · simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr (Block.preceq_trans hFmono hFH)
  have hready : H ∈
      (NamedRun.stateBeforeTime S rho t w).st.bodies ∧
      stampedBefore
        (NamedRun.stateBeforeTime S rho t w).st.core.timestamp_block
        (early S.E S.hc r p) H.erase = true ∧
      Block.find?
        (NamedRun.stateBeforeTime S rho t w).st.core.T H.root = some H.erase := by
    have hcompFE' := hcompFE
    simp only [Block.compatible, Bool.or_eq_true] at hcompFE'
    rcases hcompFE' with hHF | hFH
    · have hFmem := Proofs.NamedStoreBridge.finalizedInTree_stateBeforeTime S rho
          (early S.E S.hc r p) w
      obtain ⟨Fname, hFname, hFerase⟩ :=
        Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
          (early S.E S.hc r p) w hFmem
      have hHFn : H.erase ⪯ Fname.erase := by
        rw [hFerase]
        exact hHF
      obtain ⟨A, hAF, hAerase⟩ := Proofs.NamedAncestry.erased_ancestor_lift Fname hHFn
      obtain ⟨n, hread, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
        core.toNamedScheduleWellFormed.sorted (early S.E S.hc r p)
      change Fname ∈
        (NamedRun.stateBeforeTime S rho (early S.E S.hc r p) w).st.bodies at hFname
      have hFnameTime := hFname
      rw [hread] at hFname
      have hFnameRun := Proofs.NamedRuntime.blockInRun_of_direct S rho
        (Proofs.NamedRuntime.directBlock_of_prefix S rho hw n hFname)
      have hArun := Proofs.NamedRuntime.blockInRun_of_ancestor S rho hFnameRun hAF
      have hHrun := Proofs.NamedRuntime.blockInRun_of_direct S rho
        (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hbody)
      have hAroot : A.root = H.root := by
        have hAeraseRoot : A.erase.root = H.root := by
          rw [hAerase, Proofs.NamedWire.erase_root]
        simpa only [Proofs.NamedWire.erase_root] using hAeraseRoot
      have hAH := core.toNamedRootCollisionFree.root_injective A H hArun hHrun
        A H (Or.inl (Proofs.NamedAncestry.named_self A))
        (Or.inr (Proofs.NamedAncestry.named_self H)) hAroot
      have hAheld : A ∈
          (NamedRun.stateBeforeTime S rho (early S.E S.hc r p) w).st.bodies :=
        named_ancestor_body_mem_local
          ((Proofs.NamedRuntime.stateBeforeTime_invariants S rho
            (early S.E S.hc r p) w).1.1.1.2.2.1) hFnameTime hAF
      have hHheld : H ∈
          (NamedRun.stateBeforeTime S rho (early S.E S.hc r p) w).st.bodies := by
        rw [← hAH]
        exact hAheld
      have hstampE :=
        NamedBlockStamp.held_body_stampedBefore_stateBeforeTime S rho
          core.toNamedScheduleWellFormed w (early S.E S.hc r p) H hHheld
      obtain ⟨hheld, hstampCarry⟩ := NamedOutageClosure.q10_strict_body_carry
        S rho core.toNamedScheduleWellFormed w horder hHheld
      have hstamp : stampedBefore
          (NamedRun.stateBeforeTime S rho t w).st.core.timestamp_block
          (early S.E S.hc r p) H.erase = true := by
        unfold stampedBefore at hstampE ⊢
        rw [hstampCarry]
        exact hstampE
      have hfind := held_find_at_strict_local S core.toNamedScheduleWellFormed
        core.toNamedRootCollisionFree w hw t H hheld
      rw [Proofs.NamedWire.erase_root H] at hfind
      exact ⟨hheld, hstamp, hfind⟩
    · obtain ⟨hheldE, hstampE, -⟩ :=
        NamedHealthyHeadReady.healthy_head_body_at_read S rho core cap hdelivery
          v hv w hw H (S.a a.round) (early S.E S.hc r p)
          (early S.E S.hc r p) hHsource hdeadline le_rfl hcut hFH
      obtain ⟨hheld, hstampCarry⟩ := NamedOutageClosure.q10_strict_body_carry
        S rho core.toNamedScheduleWellFormed w horder hheldE
      have hstamp : stampedBefore
          (NamedRun.stateBeforeTime S rho t w).st.core.timestamp_block
          (early S.E S.hc r p) H.erase = true := by
        unfold stampedBefore at hstampE ⊢
        rw [hstampCarry]
        exact hstampE
      have hfind := held_find_at_strict_local S core.toNamedScheduleWellFormed
        core.toNamedRootCollisionFree w hw t H hheld
      rw [Proofs.NamedWire.erase_root H] at hfind
      exact ⟨hheld, hstamp, hfind⟩
  obtain ⟨hheld, hstamp, hfind⟩ := hready
  have hem : NamedRun.emits S rho a.val_index (Object.attest a)
      (S.a a.round) := by
    simpa only [hvote.1, hvote.2.1] using hvote.2.2
  have hactionDeadline : S.a a.round + S.E.Δ ≤ early S.E S.hc r p := hdeadline
  obtain ⟨td, hlo, hhi, j, hcall⟩ := hdelivery.broadcast a.val_index hval
    (Object.attest a) (S.a a.round) hem w hw
    (hactionDeadline.trans hcut) rfl
  have hrow := Proofs.NamedSGArrival.honest_row_after_call S rho
    core.toNamedScheduleWellFormed core.toNamedUnforgeable hval hem hcall hlo hhi
  obtain ⟨e, he, _, het⟩ := hcall.2
  obtain ⟨_, stamp, hstampBound, hstampEvent⟩ :=
    Proofs.NamedSGArrival.held_row_own_and_stamp_at_event S rho
      core.toNamedScheduleWellFormed he w a.round a hrow
  have htdEarly : td < early S.E S.hc r p := hhi.trans_le hactionDeadline
  have heEarly : e.time < early S.E S.hc r p := by
    simpa only [het] using htdEarly
  have heCut : e.time < t := heEarly.trans_le horder
  let cut := t
  let n := (rho.events.filter (fun e => decide (e.time < cut))).length
  have hread : NamedRun.stateBeforeTime S rho cut =
      NamedRun.stateBefore S rho n :=
    Proofs.Optimistic.stateBeforeTime_eq_take S core.toNamedScheduleWellFormed cut
  have hjN : j < n := by
    by_contra hnot
    have hnj : n ≤ j := Nat.le_of_not_gt hnot
    have hle := Proofs.Optimistic.le_time_of_index_ge S
      core.toNamedScheduleWellFormed (t := cut) (j := j) (e := e) hnj he
    exact (not_le_of_gt heCut) hle
  have hrowN := Proofs.NamedSGArrival.stateBefore_sg_row_stamp_mono S rho w
    (Nat.succ_le_of_lt hjN) hrow
  have hrowCut : a ∈
      (NamedRun.stateBeforeTime S rho t w).st.sg_rows a.round := by
    rw [hread]
    exact hrowN.1
  have hstampCut :
      (NamedRun.stateBeforeTime S rho t w).st.core.timestamp_sg_vote
        (Protocol.sgVote a.erase) = some (stamp : Stamp) := by
    rw [hread]
    exact hrowN.2.trans hstampEvent
  have hstampEarly : stamp < early S.E S.hc r p := hstampBound.trans_lt heEarly
  have hoccur : occurrenceBefore
      ((NamedRun.stateBeforeTime S rho t w).st.core.timestamp_sg_vote
        (Protocol.sgVote a.erase)) (early S.E S.hc r p) = true := by
    simp only [hstampCut, occurrenceBefore, decide_eq_true_eq]
    exact WithBot.coe_lt_coe.mpr hstampEarly
  have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t w).1.1.1
  have hpool := NamedAdmission.pool_view_mem _ hcoh.2.2.2.1 a hrowCut
  let target := NamedRun.stateBeforeTime S rho t w
  have hsg : Protocol.sgVote a.erase ∈
      target.st.core.toHealing.gradeView.sg_votes a.round :=
    Finset.mem_image_of_mem Protocol.sgVote hpool
  have hraw : Protocol.sgVote a.erase ∈
      rawInputs target.st.core.toHealing.gradeView S.hc.η_SG r
        (early S.E S.hc r p) v := by
    simp only [rawInputs, Finset.mem_filter]
    refine ⟨Finset.mem_biUnion.mpr ?_, ?_, hoccur⟩
    · exact ⟨a.round, List.mem_toFinset.mpr (by
        simpa only [hvote.2.1] using hk), hsg⟩
    · rw [NamedOutageClosure.sgVote_val, hvote.1]
  have hconf : (Protocol.sgVote a.erase).confirmed = some H.root := by
    rw [NamedOutageClosure.sgVote_confirmed, hconfirmed]
  have hfind' : Block.find? target.st.core.T H.root = some H.erase := by
    simpa only [target, Proofs.NamedWire.erase_root] using hfind
  have hbodyReady : bodyReady target.st.core.toHealing.gradeView target.st.core.F
      (early S.E S.hc r p) (Protocol.sgVote a.erase) = true := by
    simp only [bodyReady, hconf]
    change (match Block.find? target.st.core.T H.root with
      | none => false
      | some head => stampedBefore target.st.core.timestamp_block
          (early S.E S.hc r p) head && Block.compatible head target.st.core.F) = true
    rw [hfind', Bool.and_eq_true]
    exact ⟨hstamp, by simpa only [target] using hcompFD⟩
  refine ⟨Finset.mem_filter.mpr ⟨hraw, hbodyReady⟩, ?_, ?_, ?_⟩
  · simpa only [NamedOutageClosure.sgVote_round] using hvote.2.1
  · rw [NamedOutageClosure.sgVote_confirmed, hconfirmed, Proofs.NamedWire.erase_root]
  · exact hfind'

/-- Nonempty interpreted-input form of
`action_vote_mem_interpretedInputs_after_gst_common_upper`. -/
theorem interpretedInputs_nonempty_of_honest_window_vote_after_gst_common_upper
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {t : Time} {r k : Round} (p : Phase)
    (hk : k ∈ Protocol.latest_window S.hc.η_SG r)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {a : NamedAttestation V} {H : NamedBlock V} {C : Block V}
    (hvote : a.val_index = v ∧ a.round = k ∧
      NamedRun.emits S rho v (Object.attest a) (S.a k))
    (hhead : ∃ i : Nat, rho.events[i]? = some (.tick v (S.a k)) ∧
      H ∈ (NamedActionReads.actionReadFrom S
        (NamedRun.stateBefore S rho i v) a.round).st.bodies ∧
      a.confirmed = some H.root)
    (hHC : Block.Preceq H.erase C)
    (hFC : Block.Preceq
      (NamedRun.stateBeforeTime S rho t w).st.core.F C)
    (hpost : S.E.t_GST ≤ S.a a.round)
    (hdeadline : max (S.a a.round) S.E.t_GST + S.E.Δ ≤
      early S.E S.hc r p)
    (horder : early S.E S.hc r p ≤ t)
    (hcut : early S.E S.hc r p ≤ rho.horizon) :
    (interpretedInputs
      (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho t w).st.core.F
      S.hc.η_SG r (early S.E S.hc r p) v).Nonempty := by
  refine ⟨Protocol.sgVote a.erase, ?_⟩
  exact action_vote_mem_interpretedInputs_after_gst_common_upper
    S core p hk hv hw hvote hhead hHC hFC hpost hdeadline horder hcut

/-- Delivery-parametric exact form of the common-upper vote transport. -/
theorem interpretedInputs_nonempty_of_honest_window_vote_of_delivery_common_upper
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {cap t : Time} {r k : Round} (p : Phase)
    (hdelivery : NamedHealthyPrefixDelivery S rho cap)
    (hk : k ∈ Protocol.latest_window S.hc.η_SG r)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {a : NamedAttestation V} {H : NamedBlock V} {C : Block V}
    (hvote : a.val_index = v ∧ a.round = k ∧
      NamedRun.emits S rho v (Object.attest a) (S.a k))
    (hhead : ∃ i : Nat, rho.events[i]? = some (.tick v (S.a k)) ∧
      H ∈ (NamedActionReads.actionReadFrom S
        (NamedRun.stateBefore S rho i v) a.round).st.bodies ∧
      a.confirmed = some H.root)
    (hHC : Block.Preceq H.erase C)
    (hFC : Block.Preceq
      (NamedRun.stateBeforeTime S rho t w).st.core.F C)
    (hdeadline : S.a a.round + S.E.Δ ≤ early S.E S.hc r p)
    (horder : early S.E S.hc r p ≤ t)
    (hcut : early S.E S.hc r p ≤ cap) :
    ∃ y ∈ interpretedInputs
      (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho t w).st.core.F
      S.hc.η_SG r (early S.E S.hc r p) v,
      y.round = k ∧
      y.confirmed = some H.erase.root ∧
      Block.find?
        (NamedRun.stateBeforeTime S rho t w).st.core.T H.root = some H.erase := by
  obtain ⟨hmem, hround, hconfirmed, hfind⟩ :=
    action_vote_mem_interpretedInputs_of_delivery_common_upper S core p
      hdelivery hk hv hw hvote hhead hHC hFC hdeadline horder hcut
  exact ⟨Protocol.sgVote a.erase, hmem, hround, hconfirmed, hfind⟩











end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms exists_honest_positive_supporter_of_relativeGrade
#print axioms exists_honest_max_positive_supporter_of_relativeGrade
#print axioms windowMajorityAt_of_honestWeightMajority_of_interpreted
#print axioms windowMajorityAt_of_honestWeightMajority_of_represented
#print axioms
  action_vote_mem_interpretedInputs_after_gst_common_upper
#print axioms
  interpretedInputs_nonempty_of_honest_window_vote_after_gst_common_upper
#print axioms
  interpretedInputs_exact_of_honest_window_vote_after_gst_common_upper
#print axioms interpretedInputs_nonempty_of_honest_window_vote_of_delivery_common_upper
#print axioms DecoupledConsensusModel.Proofs.NamedRelayGuards.handled_block_held_of_finalized_prefix
end DecoupledConsensusModel.Proofs.HealingSurface

end
