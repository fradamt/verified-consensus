module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.PrefixThroughHistory
public import DecoupledConsensusInternal.Definitions.NamedJointOutage
public import DecoupledConsensusProofs.Execution.ViabilityHistory
public import DecoupledConsensusProofs.Protocol.Grades.ReadyHeadReturn
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.IntrinsicEntry
public import DecoupledConsensusProofs.Protocol.Grades.CacheProvenance

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.JointHistoryProducersTime
open Execution Internal.NamedOutageEntry Protocol
open Internal.NamedOutageEntry.History
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. Named ancestry is transitive -/

omit [Fintype V] in
theorem named_preceq_trans {A B C : NamedBlock V}
    (hAB : NamedBlock.Preceq A B) (hBC : NamedBlock.Preceq B C) :
    NamedBlock.Preceq A C := by
  induction C with
  | genesis =>
    have hB : B = .genesis := by
      simpa only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] using hBC
    exact hB ▸ hAB
  | node parent s root votes support rows proposer ih =>
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
      decide_eq_true_eq] at hBC
    rcases hBC with rfl | hBp
    · exact hAB
    · simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
      exact Or.inr (ih hBp)

/-! ## 2. The two staged reads keep the named bodies -/





/-! ## 3. Genesis is in the run scope -/

theorem univ_isQuorum (E : Env V) : E.electorate.IsQuorum (Finset.univ : Finset V) := by
  show E.electorate.finalityThreshold ≤ E.electorate.weightOf Finset.univ
  have h : E.electorate.weightOf (Finset.univ : Finset V) = E.electorate.totalWeight := rfl
  rw [h]
  show (2 * E.electorate.totalWeight + 2) / 3 ≤ E.electorate.totalWeight
  omega

theorem honest_nonempty (S : Setup V) (rho : NamedRun V)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q) :
    ∃ v : V, v ∈ rho.honest := by
  obtain ⟨v, _, hv⟩ := ViabilityHistoryTime.quorum_honest_member S rho Finset.univ
    (univ_isQuorum S.E) hbad
  exact ⟨v, hv⟩

theorem genesis_in_run (S : Setup V) (rho : NamedRun V)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q) :
    NamedRun.blockInRun S rho (.genesis : NamedBlock V) := by
  obtain ⟨v, hv⟩ := honest_nonempty S rho hbad
  have h0 : (.genesis : NamedBlock V) ∈ (NamedRun.stateBefore S rho 0 v).st.bodies := by
    show (.genesis : NamedBlock V) ∈ (NamedNode.initial : NamedNodeState V).st.bodies
    simp [NamedNode.initial, Protocol.NamedStore.initial]
  exact Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv 0 h0)

/-! ## 4a. The counting half of the SG step

`gradeBool` at the saved G2 capture plus the covered-window majority gives an
honest positive supporter, provided every honest awake validator of the window
is positive or opposing at the capture reader's view. That last input is the
delivery-side gap `honest_awake_positive_or_opposing` in `JointHistoryGaps`. -/

theorem honest_positive_of_gradeBool
    (E : Env V) (Hon : Finset V) (awake : V → Round → Bool) (etaSG r : Round)
    (gv : Protocol.GradeView V) (F : Block V) (tearly tlate : Time) (B : Block V)
    (hgrade : DecoupledConsensusModel.Protocol.gradeBool E gv F etaSG r tearly tlate B = true)
    (hwin : AwakeWindowMajority E awake Hon etaSG r)
    (hcover : ∀ v ∈ honestAwakeWindow awake Hon etaSG r,
      DecoupledConsensusModel.Protocol.positive gv F etaSG r tearly tlate v B = true ∨
        DecoupledConsensusModel.Protocol.opposing gv F etaSG r tearly tlate v B = true) :
    ∃ w ∈ Hon, DecoupledConsensusModel.Protocol.positive gv F etaSG r tearly tlate w B = true := by
  by_contra hn
  push_neg at hn
  have hlt : E.electorate.weightOf
        (Finset.univ.filter fun v =>
          DecoupledConsensusModel.Protocol.opposing gv F etaSG r tearly tlate v B = true) <
      E.electorate.weightOf
        (Finset.univ.filter fun v =>
          DecoupledConsensusModel.Protocol.positive gv F etaSG r tearly tlate v B = true) := by
    simpa only [DecoupledConsensusModel.Protocol.gradeBool, decide_eq_true_eq] using hgrade
  have hPosBad : (Finset.univ.filter fun v =>
      DecoupledConsensusModel.Protocol.positive gv F etaSG r tearly tlate v B = true) ⊆
      Finset.univ \ Hon := by
    intro v hv
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hvh => ?_⟩
    exact hn v hvh (Finset.mem_filter.mp hv).2
  have hWinOpp : honestAwakeWindow awake Hon etaSG r ⊆
      (Finset.univ.filter fun v =>
        DecoupledConsensusModel.Protocol.opposing gv F etaSG r tearly tlate v B = true) := by
    intro v hv
    have hvh : v ∈ Hon := by
      simpa only [honestAwakeWindow, Finset.mem_filter] using (Finset.mem_filter.mp hv).1
    rcases hcover v hv with hp | ho
    · exact absurd hp (hn v hvh)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ho⟩
  have h1 := E.electorate.weightOf_mono hPosBad
  have h2 := E.electorate.weightOf_mono hWinOpp
  have h3 : E.electorate.weightOf (Finset.univ \ Hon) <
      E.electorate.weightOf (honestAwakeWindow awake Hon etaSG r) := hwin
  omega

/-! ## 4b. The Q2 arm's capture bridge

`grade2_block_with` at the action read is a clipped view of a G2 root that was
frozen at this validator's own strictly earlier G2-domain tick. Everything here
is re-derived from public lemmas; the `NamedPhaseSource` versions are `private`
and are stated for `roundConfirmationRead`, not for `actionReadFrom`. -/



omit [Fintype V] in
private theorem clip_preceq (g F : Block V) : Block.Preceq (clipGrade g F) g := by
  induction g with
  | genesis => exact Block.preceq_self _
  | node p s root gv gsv ats v ih =>
    simp only [clipGrade]
    split
    · exact Block.preceq_self _
    · apply Block.preceq_trans ih
      simp only [Block.preceq, Bool.or_eq_true]
      exact Or.inr (Block.preceq_self p)

omit [Fintype V] in
private theorem clip_result_prefix (F P root : Block V)
    (result : Option (Option (Block V)))
    (hresult : clipResult F result = some (some root)) (hP : Block.Preceq P root) :
    ∃ old : Block V, result = some (some old) ∧ Block.Preceq P old := by
  cases result with
  | none => simp only [clipResult, Option.map_none, reduceCtorEq] at hresult
  | some result =>
    cases result with
    | none =>
      change (some none : Option (Option (Block V))) = some (some root) at hresult
      have hbad : (none : Option (Block V)) = some root := Option.some.inj hresult
      cases hbad
    | some old =>
      have he : clipGrade old F = root := by
        simpa only [clipResult, Option.map_some, Option.some.injEq] using hresult
      exact ⟨old, rfl, Block.preceq_trans hP (by rw [← he]; exact clip_preceq old F)⟩

omit [DecidableEq V] [Fintype V] in
private theorem align_current (c : Cache V) (s : Round) :
    (alignRound c s).current = cacheAtRound c s ∧ (alignRound c s).round = s := by
  unfold alignRound
  split_ifs with hs hn
  · exact ⟨by simp only [cacheAtRound, if_pos hs], hs.symm⟩
  · exact ⟨by simp only [cacheAtRound, if_neg hs, if_pos hn], rfl⟩
  · exact ⟨by simp only [cacheAtRound, if_neg hs, if_neg hn], rfl⟩

private theorem complete_one_other (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) (t : Time) (p q : Phase) (f : Frame V) (h : q ≠ p) :
    phaseResult (completeOne E hc st r t p f) q = phaseResult f q := by
  unfold completeOne
  split
  · rfl
  · split
    · cases p <;> cases q <;> simp_all only [putPhase, phaseResult, ne_eq, not_true_eq_false]
    · rfl

private theorem complete_frame_g2 (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (s : Round) (t : Time) (f : Frame V)
    (ht : t ≠ domain E hc s .g2) : (completeFrame E hc st s t f).g2 = f.g2 := by
  change phaseResult (completeFrame E hc st s t f) .g2 = phaseResult f .g2
  unfold completeFrame
  rw [complete_one_other E hc st s t .g0 .g2 _ (by decide),
    complete_one_other E hc st s t .g1 .g2 _ (by decide)]
  unfold completeOne
  split
  · rfl
  · simp only [if_neg ht]

/-- The G2 domain of a round is strictly before that round's action. -/
theorem action_after_g2 (S : Setup V) (s : Round) : domain S.E S.hc s .g2 < S.a s := by
  have he : S.a s = domain S.E S.hc s .g2 + 7 * S.E.Δ := by
    unfold Setup.a Protocol.HealConfig.a domain opening Phase.domainOffset
      Protocol.proposal_time Env.t slotStart
    ring
  rw [he]
  exact lt_add_of_pos_right _
    (Int.mul_pos (by decide : (0 : Int) < 7) S.E.Δ_pos)

private theorem prepared_g2_from_old (S : Setup V) (before : NamedNodeState V) (s : Round) :
    (cacheAtRound (preparedCache S before (S.a s)) s).g2 =
      clipResult before.st.core.F (cacheAtRound before.cache s).g2 := by
  let aligned := alignRound before.cache s
  have hcurrent : aligned.current = cacheAtRound before.cache s := (align_current before.cache s).1
  have hround : aligned.round = s := (align_current before.cache s).2
  have htime : S.a s ≠ domain S.E S.hc s .g2 := ne_of_gt (action_after_g2 S s)
  unfold preparedCache NamedActionReads.preparedCache onPhaseTick
  rw [Proofs.HealingLemmas.round_of_slotOf_a S s]
  change (cacheAtRound (clipCache before.st.core.F
    ⟨aligned.round,
      completeFrame S.E S.hc before.st.core.toHealing aligned.round (S.a s) aligned.current,
      completeFrame S.E S.hc before.st.core.toHealing (aligned.round + 1) (S.a s)
        aligned.next⟩) s).g2 = _
  simp only [cacheAtRound, clipCache, hround]
  change clipResult before.st.core.F
    (completeFrame S.E S.hc before.st.core.toHealing s (S.a s) aligned.current).g2 = _
  rw [complete_frame_g2 S.E S.hc before.st.core.toHealing s (S.a s) aligned.current htime, hcurrent]
  rfl

/-- **Gap B1 closed.** The action read's `Q2` is below a G2 root this same
validator froze at its own strictly earlier G2-domain tick. -/
theorem q2_capture_at_action_read (S : Setup V) (rho : NamedRun V)
    (i : Nat) (v : V) (r : Round) {q : Block V}
    (hQ : Protocol.grade2_block_with
        (NamedProfile.gradeContract (actionReadFrom S (NamedRun.stateBefore S rho i v) r).cache)
        S.E S.hc (actionReadFrom S (NamedRun.stateBefore S rho i v) r).st.core.toHealing r =
      some q) :
    ∃ (j : Nat) (raw : Block V),
      j < i ∧
      rho.events[j]? = some (.tick v (domain S.E S.hc r .g2)) ∧
      freezeRoot S.E (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
        (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG r
        (early S.E S.hc r .g2) (late S.E S.hc r .g2) = some raw ∧
      Block.Preceq q raw := by
  set before := NamedRun.stateBefore S rho i v with hbefore
  set n := actionReadFrom S before r with hn
  change grade2Block n.st.core.toHealing
    (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r) = some q at hQ
  unfold grade2Block at hQ
  split at hQ
  · rename_i hclosed
    obtain ⟨clipped, hclipped, hactive⟩ := Option.bind_eq_some_iff.mp hQ
    obtain ⟨inner, hfield, hinner⟩ := Option.bind_eq_some_iff.mp hclipped
    change inner = some clipped at hinner
    subst inner
    have hqclip : Block.Preceq q clipped :=
      (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
    change clipResult before.st.core.F (cacheAtRound n.cache r).g2 = some (some clipped) at hfield
    obtain ⟨prepared, hprepared, hqprep⟩ :=
      clip_result_prefix before.st.core.F q clipped _ hfield hqclip
    change (cacheAtRound (preparedCache S before (S.a r)) r).g2 = some (some prepared) at hprepared
    rw [prepared_g2_from_old S before r] at hprepared
    obtain ⟨old, hold, hqold⟩ :=
      clip_result_prefix before.st.core.F q prepared _ hprepared hqprep
    have hphase : phaseResult (cacheAtRound (NamedRun.stateBefore S rho i v).cache r) .g2 =
        some (some old) := hold
    rcases NamedCacheProvenance.completed_phase_origin S rho i v r .g2 (some old) hphase with
      ⟨_, hzero⟩ | ⟨j, tt, hj, he, ht, hroot⟩
    · exact absurd hzero (by simp)
    · subst tt
      obtain ⟨raw, hraw, hclip⟩ := Option.map_eq_some_iff.mp hroot.symm
      refine ⟨j, raw, hj, he, hraw, ?_⟩
      exact Block.preceq_trans hqold (by rw [← hclip]; exact clip_preceq raw _)
  · exact absurd hQ (by simp)

/-! ## 4c. Erased ancestry lifts to named ancestry inside the run scope -/

omit [Fintype V] in
theorem named_preceq_self (B : NamedBlock V) : NamedBlock.Preceq B B := by
  cases B <;> simp [NamedBlock.Preceq, NamedBlock.preceq]

theorem named_of_erase_preceq (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) {A B : NamedBlock V}
    (hA : NamedRun.blockInRun S rho A) (hB : NamedRun.blockInRun S rho B)
    (h : Block.Preceq A.erase B.erase) : NamedBlock.Preceq A B := by
  obtain ⟨A', hA'B, hA'e⟩ := ReadyHeadReturnTime.named_ancestor_of_erase A.erase B h
  have hroot : A'.root = A.root := by
    rw [← Proofs.NamedWire.erase_root A', ← Proofs.NamedWire.erase_root A, hA'e]
  have heq : A' = A := core.root_injective B A hB hA A' A (Or.inl hA'B)
    (Or.inr (named_preceq_self A)) hroot
  exact heq ▸ hA'B

/-! ## 4d. The coverage input of 4a is pure algebra plus one delivery fact

`Supports ∨ Opposes` is exhaustive as soon as the reader's early ready view of a
validator is nonempty (the late view contains the early one, and the early view
is monotone in the cutoff). So the only unproved input to the honest-supporter
extraction is that the capture reader holds at least one ready row from every
honest awake validator of the window. -/

theorem supports_or_opposes {Key BT : Type*} [DecidableEq Key]
    (covers : Key → BT → Prop)
    (tEarly tLate tRaw : Finset (DecoupledConsensusModel.Protocol.Token Key)) (b : BT)
    (hsub : tEarly ⊆ tLate) (hne : tEarly.Nonempty) :
    DecoupledConsensusModel.Protocol.Supports covers tEarly tLate tRaw b ∨
      DecoupledConsensusModel.Protocol.Opposes covers tEarly tLate tRaw b := by
  classical
  obtain ⟨u, hu, hmax⟩ := tEarly.exists_max_image DecoupledConsensusModel.Protocol.Token.round hne
  by_cases hcov : covers u.key b
  · by_cases hclean : DecoupledConsensusModel.Protocol.CleanFrom tRaw u.round
    · by_cases hlate : ∀ x ∈ tLate, u.round < x.round → covers x.key b
      · exact Or.inl ⟨u, hu, hmax, hcov, hclean, hlate⟩
      · push_neg at hlate
        obtain ⟨x, hx, hxr, hxc⟩ := hlate
        exact Or.inr (Or.inl ⟨x, hx, fun w hw => le_of_lt (lt_of_le_of_lt (hmax w hw) hxr), hxc⟩)
    · unfold DecoupledConsensusModel.Protocol.CleanFrom at hclean
      push_neg at hclean
      obtain ⟨x, hx, y, hy, hxr, hxy, hkey⟩ := hclean
      exact Or.inr (Or.inr ⟨x, hx, y, hy, fun w hw => (hmax w hw).trans hxr, hxy, hkey⟩)
  · exact Or.inr (Or.inl ⟨u, hsub hu, hmax, hcov⟩)

theorem bodyReady_mono (gv : Protocol.GradeView V) (F : Block V) {c1 c2 : Time}
    (h : c1 ≤ c2) (u : Protocol.SGVote V)
    (hu : DecoupledConsensusModel.Protocol.bodyReady gv F c1 u = true) :
    DecoupledConsensusModel.Protocol.bodyReady gv F c2 u = true := by
  unfold DecoupledConsensusModel.Protocol.bodyReady at hu ⊢
  cases hc : u.confirmed with
  | none => simp only [hc]
  | some root =>
    simp only [hc] at hu ⊢
    cases hf : Block.find? gv.T root with
    | none => simp only [hf] at hu; exact absurd hu (by simp)
    | some H =>
      simp only [hf] at hu ⊢
      obtain ⟨hstamp, hcompat⟩ := Bool.and_eq_true_iff.mp hu
      exact Bool.and_eq_true_iff.mpr ⟨occurrenceBefore_mono h hstamp, hcompat⟩

theorem readyView_mono (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    {c1 c2 : Time} (h : c1 ≤ c2) (v : V) :
    readyView gv F eta r c1 v ⊆ readyView gv F eta r c2 v := by
  refine Finset.image_subset_image ?_
  intro u hu
  simp only [DecoupledConsensusModel.Protocol.interpretedInputs, DecoupledConsensusModel.Protocol.rawInputs,
    Finset.mem_filter] at hu ⊢
  exact ⟨⟨hu.1.1, hu.1.2.1, occurrenceBefore_mono h hu.1.2.2⟩,
    bodyReady_mono gv F h u hu.2⟩

theorem early_le_late_g2 (S : Setup V) (r : Round) :
    early S.E S.hc r .g2 ≤ late S.E S.hc r .g2 := by
  have he : late S.E S.hc r .g2 = early S.E S.hc r .g2 + 4 * S.E.Δ := by
    unfold early late Phase.earlyOffset Phase.lateOffset
    ring
  rw [he]
  exact le_add_of_nonneg_right
    (le_of_lt (Int.mul_pos (by decide : (0 : Int) < 4) S.E.Δ_pos))

omit [Fintype V] in
theorem positive_or_opposing (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    (tearly tlate : Time) (v : V) (B : Block V)
    (hsub : readyView gv F eta r tearly v ⊆ readyView gv F eta r tlate v)
    (hne : (readyView gv F eta r tearly v).Nonempty) :
    positive gv F eta r tearly tlate v B = true ∨
      opposing gv F eta r tearly tlate v B = true := by
  rcases supports_or_opposes (fun k b => localCovers gv k b = true)
      (readyView gv F eta r tearly v) (readyView gv F eta r tlate v)
      (rawView gv eta r tlate v) B hsub hne with hpos | hopp
  · exact Or.inl (by simpa only [positive, decide_eq_true_eq] using hpos)
  · exact Or.inr (by simpa only [opposing, decide_eq_true_eq] using hopp)

/-- The honest-supporter extraction, reduced to one delivery statement:
the capture reader's early ready view of each honest awake window validator
is nonempty. -/
theorem honest_positive_of_gradeBool_ready
    (S : Setup V) (Hon : Finset V) (awake : V → Round → Bool) (r : Round)
    (gv : Protocol.GradeView V) (F B : Block V)
    (hgrade : gradeBool S.E gv F S.hc.η_SG r
      (early S.E S.hc r .g2) (late S.E S.hc r .g2) B = true)
    (hwin : AwakeWindowMajority S.E awake Hon S.hc.η_SG r)
    (hready : ∀ v ∈ honestAwakeWindow awake Hon S.hc.η_SG r,
      (readyView gv F S.hc.η_SG r (early S.E S.hc r .g2) v).Nonempty) :
    ∃ w ∈ Hon, positive gv F S.hc.η_SG r
      (early S.E S.hc r .g2) (late S.E S.hc r .g2) w B = true :=
  honest_positive_of_gradeBool S.E Hon awake S.hc.η_SG r gv F _ _ B hgrade hwin
    (fun v hv => positive_or_opposing gv F S.hc.η_SG r _ _ v B
      (readyView_mono gv F S.hc.η_SG r (early_le_late_g2 S r) v) (hready v hv))

#print axioms supports_or_opposes
#print axioms honest_positive_of_gradeBool_ready
#print axioms genesis_in_run
#print axioms honest_positive_of_gradeBool
#print axioms q2_capture_at_action_read
#print axioms named_of_erase_preceq
#print axioms action_after_g2
end DecoupledConsensusModel.Proofs.NamedOutageHistory.JointHistoryProducersTime

end
