module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.WeakGoldfishCone
public import DecoupledConsensusProofs.Protocol.Grades.FrameCompleted

@[expose] public section

/-!
# SG read compatibility with a general history start

The retained window can start at genesis or after an expiry interval.
Round zero uses its root directly, not an empty-window majority.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakSG

open Internal Execution Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem ancestorCompatible {A C B : Block V}
    (hAC : Block.Preceq A C) (hCB : Block.compatible C B = true) :
    Block.compatible A B = true := by
  have hcases : Block.Preceq C B ∨ Block.Preceq B C := by
    simpa only [Block.compatible, Bool.or_eq_true] using hCB
  rcases hcases with h | h
  · simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inl (Block.preceq_trans hAC h)
  · exact Block.compatible_of_preceq_common hAC h

private theorem gradeCompatibleOfBatch
    (E : Env V) {gv : Protocol.GradeView V}
    {hc : Protocol.HealConfig} {F : Block V} {Hon : Finset V}
    {r : Round} {B X : Block V} {p : DecoupledConsensusModel.Protocol.Phase}
    (hbatch : Internal.PhaseGrades.BatchCompatibleAt hc gv F Hon r
      (DecoupledConsensusModel.Protocol.late E hc r p) B)
    (hmajority : Internal.PhaseGrades.WindowMajorityAt E hc gv F Hon r
      (DecoupledConsensusModel.Protocol.late E hc r p))
    (hgrade : Internal.PhaseGrades.phaseGrade E hc gv F r p X = true) :
    Block.compatible X B = true := by
  by_contra hn
  have hconf : Block.conflicts X B = true := by
    rw [Bool.not_eq_true] at hn
    simp only [Block.conflicts, hn, Bool.not_false]
  have hfalse := Proofs.HealingLemmas.q7_grade_eq_false_of_conflicts
    E hc gv F Hon r B X p hbatch hmajority hconf
  rw [hfalse] at hgrade
  cases hgrade
theorem getSgRoot_compatible_of_windowHistory_at_read
    (S : Setup V) (n : NamedNodeState V) (r : Round) (B : Block V)
    {Hon : Finset V}
    (hbatch : Internal.PhaseGrades.BatchCompatibleAt S.hc
      n.st.core.toHealing.gradeView n.st.core.F Hon r
      (DecoupledConsensusModel.Protocol.late S.E S.hc r .g1) B)
    (hmajority : Internal.PhaseGrades.WindowMajorityAt S.E S.hc
      n.st.core.toHealing.gradeView n.st.core.F Hon r
      (DecoupledConsensusModel.Protocol.late S.E S.hc r .g1))
    (hgrade : ∀ raw, (DecoupledConsensusModel.Protocol.readFrame n.cache
      n.st.core.toHealing r).g1 = some (some raw) →
      Internal.PhaseGrades.phaseGrade S.E S.hc n.st.core.toHealing.gradeView
        n.st.core.F r .g1 raw = true)
    (hroot : Block.compatible
      (Protocol.get_fg_root n.st.core.toHealing.toFG) B = true) :
    Block.compatible
      (Protocol.get_sg_root_with (NamedProfile.gradeContract n.cache)
        S.E S.hc n.st.core.toHealing r) B = true := by
  change Block.compatible
    (DecoupledConsensusModel.Protocol.anchor S.E S.hc n.st.core.toHealing r
      (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g1)
      B = true
  cases hframe :
      (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g1 with
  | none => exact hroot
  | some x =>
      cases x with
      | none => exact hroot
      | some raw =>
          have hcompat := gradeCompatibleOfBatch S.E hbatch hmajority
            (hgrade raw hframe)
          unfold DecoupledConsensusModel.Protocol.anchor
          simp only [Option.getD]
          cases hA : DecoupledConsensusModel.Protocol.activePrefix
              (Protocol.get_filtered_block_tree
                n.st.core.toHealing.toFG) raw with
          | none => exact hroot
          | some A =>
              have hpre : Block.Preceq A raw := by
                unfold DecoupledConsensusModel.Protocol.activePrefix at hA
                exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hA)).2
              exact ancestorCompatible hpre hcompat

#print axioms getSgRoot_compatible_of_windowHistory_at_read

/- The retained SG-history roots are lifted to the interpreted-input shape used
by the prepared relative-grade read. -/


/- The awake-window margin becomes the prepared reader margin once every awake
source has an interpreted input. -/
theorem windowMajorityAt_of_awakeWindowMajority
    (S : Setup V) {gv : Protocol.GradeView V} {F : Block V} {Hon : Finset V}
    {r : Round} {cutoff : Time}
    (hwindow : AwakeWindowMajority S.E (fun v => (S.node v).awake)
      Hon S.hc.η_SG r)
    (hinterpreted : ∀ v ∈ honestAwakeWindow (fun v => (S.node v).awake)
      Hon S.hc.η_SG r,
      (DecoupledConsensusModel.Protocol.interpretedInputs gv F S.hc.η_SG r cutoff v).Nonempty) :
    Internal.PhaseGrades.WindowMajorityAt S.E S.hc gv F Hon r cutoff := by
  unfold Internal.PhaseGrades.WindowMajorityAt Internal.PhaseGrades.honestPresent
  apply lt_of_lt_of_le hwindow
  apply S.E.electorate.weightOf_mono
  intro v hv
  have hv' : v ∈ honestAwakeWindow (fun v => (S.node v).awake)
      Hon S.hc.η_SG r := hv
  simp only [honestAwakeWindow, Finset.mem_filter] at hv
  exact Finset.mem_filter.mpr ⟨hv.1, hinterpreted v hv'⟩

#print axioms windowMajorityAt_of_awakeWindowMajority

omit [Fintype V] in
private theorem clipGrade_preceq (g F : Block V) :
    Block.Preceq (DecoupledConsensusModel.Protocol.clipGrade g F) g := by
  induction g with
  | genesis => exact Block.preceq_self _
  | node p s root gv gsv ats v ih =>
      simp only [DecoupledConsensusModel.Protocol.clipGrade]
      split
      · exact Block.preceq_self _
      · exact Block.preceq_trans ih (by
          simp only [Block.preceq, Bool.or_eq_true]
          exact Or.inr (Block.preceq_self _))

omit [Fintype V] in
private theorem headCoversOfPreceq {T : Finset (Block V)} {A C : Block V}
    {h : Option BlockId} (hAC : Block.Preceq A C)
    (hcov : Protocol.head_covers T C h = true) :
    Protocol.head_covers T A h = true := by
  unfold Protocol.head_covers at hcov ⊢
  cases h with
  | none => exact hcov
  | some root =>
      dsimp only at hcov ⊢
      cases hfind : Block.find? T root with
      | none =>
          rw [hfind] at hcov
          exact absurd hcov (by simp)
      | some head =>
          rw [hfind] at hcov
          dsimp only at hcov ⊢
          exact Block.preceq_trans hAC hcov

omit [Fintype V] in
private theorem positiveOfPreceq {A C : Block V} (hAC : Block.Preceq A C)
    (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    (early late : Time) (v : V)
    (hC : DecoupledConsensusModel.Protocol.positive gv F eta r early late v C = true) :
    DecoupledConsensusModel.Protocol.positive gv F eta r early late v A = true := by
  simp only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq] at hC ⊢
  rcases hC with ⟨u, hu, hmax, hcov, hclean, hlate⟩
  refine ⟨u, hu, hmax, headCoversOfPreceq hAC hcov, hclean, ?_⟩
  intro x hx hlt
  exact headCoversOfPreceq hAC (hlate x hx hlt)

omit [Fintype V] in
private theorem opposingOfPreceq {A C : Block V} (hAC : Block.Preceq A C)
    (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    (early late : Time) (v : V)
    (hA : DecoupledConsensusModel.Protocol.opposing gv F eta r early late v A = true) :
    DecoupledConsensusModel.Protocol.opposing gv F eta r early late v C = true := by
  simp only [DecoupledConsensusModel.Protocol.opposing, decide_eq_true_eq] at hA ⊢
  rcases hA with ⟨x, hx, hmax, hnot⟩ | ⟨x, hx, y, hy, hmax, heq, hkey⟩
  · left
    refine ⟨x, hx, hmax, ?_⟩
    intro hcov
    exact hnot (headCoversOfPreceq hAC hcov)
  · exact Or.inr ⟨x, hx, y, hy, hmax, heq, hkey⟩

private theorem phaseGrade_of_preceq_local
    (E : Env V) (hc : Protocol.HealConfig) (gv : Protocol.GradeView V)
    (F : Block V) (r : Round) (p : DecoupledConsensusModel.Protocol.Phase) {A C : Block V}
    (hAC : Block.Preceq A C)
    (hC : Internal.PhaseGrades.phaseGrade E hc gv F r p C = true) :
    Internal.PhaseGrades.phaseGrade E hc gv F r p A = true := by
  simp only [Internal.PhaseGrades.phaseGrade, DecoupledConsensusModel.Protocol.gradeBool,
    decide_eq_true_eq] at hC ⊢
  have hOpp : (Finset.univ.filter fun v =>
      DecoupledConsensusModel.Protocol.opposing gv F hc.η_SG r
        (DecoupledConsensusModel.Protocol.early E hc r p) (DecoupledConsensusModel.Protocol.late E hc r p) v A = true) ⊆
      Finset.univ.filter fun v =>
      DecoupledConsensusModel.Protocol.opposing gv F hc.η_SG r
          (DecoupledConsensusModel.Protocol.early E hc r p) (DecoupledConsensusModel.Protocol.late E hc r p) v C = true := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,
      opposingOfPreceq hAC gv F hc.η_SG r
        (DecoupledConsensusModel.Protocol.early E hc r p)
        (DecoupledConsensusModel.Protocol.late E hc r p) v
        (Finset.mem_filter.mp hv).2⟩
  have hPos : (Finset.univ.filter fun v =>
      DecoupledConsensusModel.Protocol.positive gv F hc.η_SG r
        (DecoupledConsensusModel.Protocol.early E hc r p) (DecoupledConsensusModel.Protocol.late E hc r p) v C = true) ⊆
      Finset.univ.filter fun v =>
        DecoupledConsensusModel.Protocol.positive gv F hc.η_SG r
          (DecoupledConsensusModel.Protocol.early E hc r p) (DecoupledConsensusModel.Protocol.late E hc r p) v A = true := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,
      positiveOfPreceq hAC gv F hc.η_SG r
        (DecoupledConsensusModel.Protocol.early E hc r p)
        (DecoupledConsensusModel.Protocol.late E hc r p) v
        (Finset.mem_filter.mp hv).2⟩
  exact lt_of_le_of_lt (E.electorate.weightOf_mono hOpp)
    (lt_of_lt_of_le hC (E.electorate.weightOf_mono hPos))

/- A completed prepared G1 frame result is a grade at the domain read that
formed that frame. -/
theorem phaseGrade_of_preparedFrame_g1
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (w : V) (hw : w ∈ rho.honest) (r : Round) (hr : 0 < r) (t : Time)
    (hround : S.hc.round_of (S.E.slotOf t) = r)
    (ht : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 < t)
    (hta : t ≤ DecoupledConsensusModel.Protocol.opening S.E S.hc (r + 1))
    (htick : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 ≤ rho.horizon)
    {raw : Block V}
    (hframe :
      (DecoupledConsensusModel.Protocol.readFrame
        (NamedActionReads.confirmationReadAt S rho w t).cache
        (NamedActionReads.confirmationReadAt S rho w t).st.core.toHealing r).g1 =
        some (some raw)) :
    Internal.PhaseGrades.phaseGrade S.E S.hc
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F r .g1 raw = true := by
  have hcompleted := FrameCompleted.frame_phase_completed_in_round S rho core w hw r hr .g1 t
    ht hta htick
  have hprepared := NamedOutageClosure.frame_phase_prepared_eq S rho w r .g1 t hround _
    hcompleted
  have hmap := Option.some_inj.mp (hprepared.symm.trans hframe)
  obtain ⟨grade, hgrade, hclip⟩ := Option.map_eq_some_iff.mp hmap
  have hmem := Proofs.Engine.deepest?_mem hgrade
  have hgraded := (Finset.mem_filter.mp hmem).2
  have hancestor := phaseGrade_of_preceq_local S.E S.hc
    (NamedRun.stateBeforeTime S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
    (NamedRun.stateBeforeTime S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F r .g1
    (clipGrade_preceq grade
      (NamedRun.stateBeforeTime S rho t w).st.core.F) hgraded
  simpa only [hclip] using hancestor

#print axioms phaseGrade_of_preparedFrame_g1










/- Compatible retained emissions protect the SG root, including round zero. -/

/-
/-- Compatible retained emissions protect the SG root, including round zero. -/
theorem getSgRoot_compatible_of_windowHistory_at_read
    (S: Setup V) {rho: Run V} (adm: AdmissibleCore S rho)
    (hmajority: HonestWeightMajority S rho.honest)
    {base r: Round} {B: Block V} (hspan: base ≤ r - S.hc.η_SG)
    (hhistory: ∀ k, base ≤ k → k < r → HonestSGEmissionsCompatibleAtRound S rho k B)
    {w: V} (hw: w ∈ rho.honest) {time: Time}
    (hwindow: 0 < r → 2 * S.E.electorate.weightOf
        (Protocol.represented_set
          (rho.storeBeforeTime S w time).toHealing.sg_votes S.hc.η_SG r \ rho.honest) <
      Protocol.W_r S.E (rho.storeBeforeTime S w time).toHealing.sg_votes S.hc.η_SG r)
    (hroot: Block.compatible
      (Protocol.get_fg_root (rho.storeBeforeTime S w time).toHealing.toFG) B = true):
    Block.compatible (Protocol.get_sg_root S.E S.hc
      (rho.storeBeforeTime S w time).toHealing r) B = true:= by
  by_cases hrzero: r = 0
  · subst r
    rw [get_sg_root_zero]
    exact hroot
  · have hr: 0 < r:= Nat.pos_of_ne_zero hrzero
    have hprev: base ≤ r - 1:= hspan.trans (Nat.sub_le_sub_left S.hc.η_SG_ge_one r)
    have hbatch:= batchCompatible_at_read_of_emittedSGHistory S adm hw
      (time:= time) (hhistory (r - 1) hprev (Nat.sub_lt hr (by decide)))
    rw [Nat.sub_add_cancel hr] at hbatch
    apply getSgRoot_compatible_of_batch_and_window S.E
      (Protocol.HonestWeightMajority.faulty_lt_m hmajority) hbatch (hwindow hr) ?_ hroot
    intro k hk u hu huh
    exact rootCompatible_of_emittedSGHistory_at_read S adm hw
      (hhistory k (hspan.trans (mem_latestWindow_lower_bound hk))
        (mem_latestWindow_lt hk)) hu huh

/-- The Goldfish cone step uses the same SG history at genesis and after expiry. -/
theorem goldfishCone_succ_of_windowSGHistory
    (S: Setup V) {rho: Run V} (adm: AdmissibleCore S rho)
    (hcom: HonestCommittees S rho.honest)
    (hmajority: HonestWeightMajority S rho.honest)
    {base: Round} {s: Slot} {B: Block V} (hs: 0 < s)
    (hpost: S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor: Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hvotes: HonestVotesCone S rho s (fun X => Block.Preceq B X))
    (hspan: base ≤ S.hc.round_of (s + 1) - S.hc.η_SG)
    (hhistory: ∀ k, base ≤ k → k < S.hc.round_of (s + 1) →
      HonestSGEmissionsCompatibleAtRound S rho k B)
    (hwindow: 0 < S.hc.round_of (s + 1) → ∀ w ∈ rho.honest,
      2 * S.E.electorate.weightOf
        (Protocol.represented_set (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.sg_votes
          S.hc.η_SG (S.hc.round_of (s + 1)) \ rho.honest) <
      Protocol.W_r S.E (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.sg_votes
        S.hc.η_SG (S.hc.round_of (s + 1)))
    (hwitnesses: ∀ w ∈ rho.honest,
      (derived_state S.E S.cfg B).h < (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).h_max - 1 →
      FGFrontierWitnessesCompatibleAt S rho w (s + 1) B)
    (hroots: ∀ w ∈ rho.honest, Block.compatible
      (Protocol.get_fg_root (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) B =
        true):
    (∀ w ∈ rho.honest, Block.Preceq B (voteDutyHead S rho w (s + 1))) ∧
      HonestVotesCone S rho (s + 1) (fun X => Block.Preceq B X):= by
  apply WeakGoldfish.goldfishCone_succ_of_frontierWitnesses S adm hcom hmajority hs hpost hhor
    hvotes hwitnesses hroots
  intro w hw
  have hanchor:= getSgRoot_compatible_of_windowHistory_at_read S adm hmajority hspan hhistory
    hw (time:= Protocol.vote_time S.E (s + 1)) (fun hr => hwindow hr w hw) (hroots w hw)
  rw [healAnchor_eq_get_sg_root,
    show (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s = s + 1 from
      voteDutyStore_slot S rho w (s + 1)]
  exact hanchor

 -/

end WeakSG
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
