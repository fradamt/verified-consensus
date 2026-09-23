module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.Runtime
public import DecoupledConsensusProofs.Protocol.Handlers.FinalityMonotone

@[expose] public section

/-! Actual named-cache capture origins. Pure completion and clipping
arguments are reused without importing the resilience research closure.
Event-index origins and strict chronological reads are separate results. -/
namespace DecoupledConsensusModel.Proofs.NamedCacheProvenance
open Execution DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V]

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

private theorem clip_compatible (g F : Block V) : Block.compatible (clipGrade g F) F = true := by
  induction g with
  | genesis => simp [clipGrade, Block.compatible, Protocol.preceq_genesis]
  | node p s root gv gsv ats v ih =>
    simp only [clipGrade]
    split
    · assumption
    · exact ih

private theorem retained_prefix (g F B : Block V) (hBF : Block.compatible B F = true) :
    Block.Preceq B (clipGrade g F) ↔ Block.Preceq B g := by
  constructor
  · intro h
    exact Block.preceq_trans h (clip_preceq g F)
  · induction g with
    | genesis => exact fun h => h
    | node p s root gv gsv ats v ih =>
      intro hBg
      by_cases hGF : Block.compatible (.node p s root gv gsv ats v) F = true
      · simpa only [clipGrade, hGF, ↓reduceIte] using hBg
      · have hBp : Block.Preceq B p := by
          simp only [Block.Preceq, Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at hBg
          rcases hBg with hEq | hBp
          · subst B
            exact False.elim (hGF hBF)
          · exact hBp
        simpa only [clipGrade, hGF, Bool.eq_false_iff.mpr hGF, ↓reduceIte] using ih hBp

private theorem compatible_ancestors {A B C D : Block V}
    (hAB : Block.Preceq A B) (hCD : Block.Preceq C D)
    (hBD : Block.compatible B D = true) : Block.compatible A C = true := by
  simp only [Block.compatible, Bool.or_eq_true] at hBD
  rcases hBD with hBD | hDB
  · exact Block.compatible_of_preceq_common (Block.preceq_trans hAB hBD) hCD
  · exact Block.compatible_of_preceq_common hAB (Block.preceq_trans hCD hDB)

private theorem clip_after_advance (B F G : Block V) (hFG : Block.Preceq F G) :
    clipGrade (clipGrade B F) G = clipGrade B G := by
  apply Block.preceq_antisymm
  · apply (retained_prefix B G _ (clip_compatible (clipGrade B F) G)).mpr
    exact Block.preceq_trans (clip_preceq (clipGrade B F) G) (clip_preceq B F)
  · apply (retained_prefix (clipGrade B F) G _ (clip_compatible B G)).mpr
    apply (retained_prefix B F _ ?_).mpr
    · exact clip_preceq B G
    · exact compatible_ancestors (Block.preceq_self _) hFG (clip_compatible B G)

private theorem map_clip_after_advance (root : Option (Block V)) (F G : Block V)
    (hFG : Block.Preceq F G) :
    (root.map (fun B => clipGrade B F)).map (fun B => clipGrade B G) =
      root.map (fun B => clipGrade B G) := by
  cases root with
  | none => rfl
  | some B => exact congrArg some (clip_after_advance B F G hFG)

private def FrameClaim (r : Round) (f : Frame V)
    (P : Round → Phase → Option (Block V) → Prop) : Prop :=
  ∀ p root, phaseResult f p = some root → P r p root

private def CacheClaim (c : Cache V)
    (P : Round → Phase → Option (Block V) → Prop) : Prop :=
  FrameClaim c.round c.current P ∧ FrameClaim (c.round + 1) c.next P

omit [DecidableEq V] in
private theorem pending_claim (r : Round) (P : Round → Phase → Option (Block V) → Prop) :
    FrameClaim r (pendingFrame : Frame V) P := by
  intro p root h
  cases p <;> cases h

omit [DecidableEq V] in
private theorem cache_claim_mono (c : Cache V)
    (P Q : Round → Phase → Option (Block V) → Prop)
    (h : CacheClaim c P) (hPQ : ∀ r p root, P r p root → Q r p root) : CacheClaim c Q :=
  ⟨fun p root hp => hPQ _ p root (h.1 p root hp),
    fun p root hp => hPQ _ p root (h.2 p root hp)⟩

omit [DecidableEq V] in
private theorem align_claim (c : Cache V) (r : Round)
    (P : Round → Phase → Option (Block V) → Prop) (h : CacheClaim c P) :
    CacheClaim (alignRound c r) P := by
  unfold alignRound
  split_ifs with hsame hnext
  · exact h
  · subst r
    exact ⟨h.2, pending_claim _ P⟩
  · exact ⟨pending_claim _ P, pending_claim _ P⟩

private theorem result_clip_frame (F : Block V) (f : Frame V) (p : Phase) :
    phaseResult (clipFrame F f) p = clipResult F (phaseResult f p) := by
  cases p <;> rfl

private theorem clip_frame_claim (F : Block V) (r : Round) (f : Frame V)
    (P Q : Round → Phase → Option (Block V) → Prop) (h : FrameClaim r f P)
    (hPQ : ∀ p root, P r p root → Q r p (root.map (fun B => clipGrade B F))) :
    FrameClaim r (clipFrame F f) Q := by
  intro p result hresult
  rw [result_clip_frame] at hresult
  cases hs : phaseResult f p with
  | none => simp only [hs, clipResult, Option.map_none, reduceCtorEq] at hresult
  | some root =>
    have he : root.map (fun B => clipGrade B F) = result := by
      simpa only [hs, clipResult, Option.map_some, Option.some.injEq] using hresult
    exact he ▸ hPQ p root (h p root hs)

private theorem clip_cache_claim (F : Block V) (c : Cache V)
    (P Q : Round → Phase → Option (Block V) → Prop) (h : CacheClaim c P)
    (hPQ : ∀ r p root, P r p root → Q r p (root.map (fun B => clipGrade B F))) :
    CacheClaim (clipCache F c) Q :=
  ⟨clip_frame_claim F _ _ P Q h.1 (hPQ c.round),
    clip_frame_claim F _ _ P Q h.2 (hPQ (c.round + 1))⟩

private theorem complete_one_other [Fintype V] (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) (t : Time) (p q : Phase) (f : Frame V) (h : q ≠ p) :
    phaseResult (completeOne E hc st r t p f) q = phaseResult f q := by
  unfold completeOne
  split
  · rfl
  · split
    · cases p <;> cases q <;> simp_all only [putPhase, phaseResult, ne_eq, not_true_eq_false]
    · rfl

private theorem complete_one_claim [Fintype V] (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) (t : Time) (p : Phase) (f : Frame V)
    (P : Round → Phase → Option (Block V) → Prop) (h : FrameClaim r f P)
    (hnew : ∀ q, t = domain E hc r q →
      P r q (freezeRoot E st.gradeView st.F hc.η_SG r (early E hc r q) (late E hc r q))) :
    FrameClaim r (completeOne E hc st r t p f) P := by
  intro q root hroot
  by_cases hqp : q = p
  · subst q
    unfold completeOne at hroot
    split at hroot
    · exact h p root hroot
    · split at hroot
      · rename_i htime
        have he : freezeRoot E st.gradeView st.F hc.η_SG r
            (early E hc r p) (late E hc r p) = root := by
          cases p <;> exact Option.some.inj hroot
        exact he ▸ hnew p htime
      · exact h p root hroot
  · rw [complete_one_other E hc st r t p q f hqp] at hroot
    exact h q root hroot

private theorem complete_frame_claim [Fintype V] (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) (t : Time) (f : Frame V)
    (P : Round → Phase → Option (Block V) → Prop) (h : FrameClaim r f P)
    (hnew : ∀ q, t = domain E hc r q →
      P r q (freezeRoot E st.gradeView st.F hc.η_SG r (early E hc r q) (late E hc r q))) :
    FrameClaim r (completeFrame E hc st r t f) P :=
  complete_one_claim E hc st r t .g0 _ P
    (complete_one_claim E hc st r t .g1 _ P
      (complete_one_claim E hc st r t .g2 f P h hnew) hnew) hnew

omit [DecidableEq V] in
private theorem cache_lookup_claim (c : Cache V)
    (P : Round → Phase → Option (Block V) → Prop) (h : CacheClaim c P)
    (r : Round) (p : Phase) (root : Option (Block V))
    (hroot : phaseResult (cacheAtRound c r) p = some root) : P r p root := by
  unfold cacheAtRound at hroot
  split_ifs at hroot with hcurrent hnext
  · subst r
    exact h.1 p root hroot
  · subst r
    exact h.2 p root hroot
  · exact pending_claim r P p root hroot

variable [Fintype V]

/-- A completed result comes from the actual initial empty frame or one
earlier local capture, clipped to the current finalized root. -/
def Origin (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V)
    (r : Round) (p : Phase) (root : Option (Block V)) (F : Block V) : Prop :=
  (r = 0 ∧ root = none) ∨ ∃ (j : Nat) (t : Time),
    j < i ∧ rho.events[j]? = some (.tick v t) ∧ t = domain S.E S.hc r p ∧
    root = (freezeRoot S.E
      (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
      (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG r
      (early S.E S.hc r p) (late S.E S.hc r p)).map (fun B => clipGrade B F)

private theorem origin_index_mono (S : Setup V) (rho : NamedRun V)
    (i k : Nat) (v : V) (r : Round) (p : Phase) (root : Option (Block V)) (F : Block V)
    (hik : i ≤ k) (h : Origin S rho i v r p root F) : Origin S rho k v r p root F := by
  rcases h with hzero | ⟨j, t, hj, he, ht, hr⟩
  · exact Or.inl hzero
  · exact Or.inr ⟨j, t, hj.trans_le hik, he, ht, hr⟩

private theorem origin_clip (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V)
    (r : Round) (p : Phase) (root : Option (Block V)) (F G : Block V)
    (hFG : Block.Preceq F G) (h : Origin S rho i v r p root F) :
    Origin S rho i v r p (root.map (fun B => clipGrade B G)) G := by
  rcases h with ⟨hr, hroot⟩ | ⟨j, t, hj, he, ht, hroot⟩
  · exact Or.inl ⟨hr, by rw [hroot]; rfl⟩
  · refine Or.inr ⟨j, t, hj, he, ht, ?_⟩
    rw [hroot, map_clip_after_advance _ F G hFG]

private theorem initial_claim (S : Setup V) (rho : NamedRun V) (v : V) :
    CacheClaim (NamedWorld.init v).cache
      (fun r p root => Origin S rho 0 v r p root (NamedWorld.init v).st.core.F) := by
  constructor
  · intro p root hroot
    have hr : root = none := by cases p <;> exact (Option.some.inj hroot).symm
    exact Or.inl ⟨rfl, hr⟩
  · exact pending_claim _ _

private theorem tick_claim (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V) (t : Time)
    (he : rho.events[i]? = some (.tick v t))
    (h : CacheClaim (NamedRun.stateBefore S rho i v).cache
      (fun r p root => Origin S rho i v r p root
        (NamedRun.stateBefore S rho i v).st.core.F)) :
    CacheClaim (Execution.NamedNode.tick S v (NamedRun.stateBefore S rho i v) t).1.cache
      (fun r p root => Origin S rho (i + 1) v r p root
        (Execution.NamedNode.tick S v (NamedRun.stateBefore S rho i v) t).1.st.core.F) := by
  let n := NamedRun.stateBefore S rho i v
  let P : Round → Phase → Option (Block V) → Prop := fun r p root => Origin S rho (i + 1) v r p
    (root.map (fun B => clipGrade B n.st.core.F)) n.st.core.F
  have hpre : CacheClaim n.cache P := by
    apply cache_claim_mono n.cache _ P h
    intro r p root horigin
    exact origin_clip S rho (i + 1) v r p root _ _ (Block.preceq_self _)
      (origin_index_mono S rho i (i + 1) v r p root _ (Nat.le_succ i) horigin)
  let aligned := alignRound n.cache (S.hc.round_of (S.E.slotOf t))
  have haligned : CacheClaim aligned P := align_claim n.cache _ P hpre
  have hnew : ∀ r p, t = domain S.E S.hc r p →
      P r p (freezeRoot S.E n.st.core.toHealing.gradeView n.st.core.F S.hc.η_SG r
        (early S.E S.hc r p) (late S.E S.hc r p)) := by
    intro r p ht
    exact Or.inr ⟨i, t, Nat.lt_succ_self i, he, ht, rfl⟩
  have hcompleted : CacheClaim
      ⟨aligned.round, completeFrame S.E S.hc n.st.core.toHealing aligned.round t aligned.current,
        completeFrame S.E S.hc n.st.core.toHealing (aligned.round + 1) t aligned.next⟩ P :=
    ⟨complete_frame_claim S.E S.hc n.st.core.toHealing _ t _ P haligned.1 (hnew _),
      complete_frame_claim S.E S.hc n.st.core.toHealing _ t _ P haligned.2 (hnew _)⟩
  have hprepared : CacheClaim (onPhaseTick S.E S.hc n.st.core.toHealing t n.cache)
      (fun r p root => Origin S rho (i + 1) v r p root n.st.core.F) := by
    exact clip_cache_claim n.st.core.F _ P _ hcompleted (fun _ _ _ hp => hp)
  rw [NamedNode.tick_cache_eq]
  exact clip_cache_claim _ _ _ _ hprepared (fun r p root horigin =>
    origin_clip S rho (i + 1) v r p root _ _
      (NamedFinalityMonotone.node_tick_F S v n t) horigin)

private theorem process_claim (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V)
    (o : NamedObject V)
    (h : CacheClaim (NamedRun.stateBefore S rho i v).cache
      (fun r p root => Origin S rho i v r p root
        (NamedRun.stateBefore S rho i v).st.core.F)) :
    CacheClaim (Execution.NamedNode.process S (NamedRun.stateBefore S rho i v) o).cache
      (fun r p root => Origin S rho (i + 1) v r p root
        (Execution.NamedNode.process S (NamedRun.stateBefore S rho i v) o).st.core.F) := by
  rw [NamedNode.process_cache_eq]
  apply clip_cache_claim _ _ _ _ h
  intro r p root horigin
  exact origin_clip S rho (i + 1) v r p root _ _
    (NamedFinalityMonotone.node_process_F S _ o)
    (origin_index_mono S rho i (i + 1) v r p root _ (Nat.le_succ i) horigin)

private theorem prefix_claim (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V) :
    CacheClaim (NamedRun.stateBefore S rho i v).cache
      (fun r p root => Origin S rho i v r p root
        (NamedRun.stateBefore S rho i v).st.core.F) := by
  induction i with
  | zero => exact initial_claim S rho v
  | succ i ih =>
    have carry : CacheClaim (NamedRun.stateBefore S rho i v).cache
        (fun r p root => Origin S rho (i + 1) v r p root
          (NamedRun.stateBefore S rho i v).st.core.F) :=
      cache_claim_mono _ _ _ ih (fun r p root h =>
        origin_index_mono S rho i (i + 1) v r p root _ (Nat.le_succ i) h)
    rw [Proofs.NamedRuntime.stateBefore_succ]
    cases he : rho.events[i]? with
    | none => simpa only [he, Option.toList_none, List.foldl_nil] using carry
    | some e =>
      simp only [Option.toList_some, List.foldl_cons, List.foldl_nil]
      cases e with
      | tick u t =>
        by_cases hvu : v = u
        · subst u
          simpa only [NamedWorld.step, Function.update_self] using tick_claim S rho i v t he ih
        · simpa only [NamedWorld.step, Function.update_of_ne hvu] using carry
      | deliver u o t =>
        by_cases hvu : v = u
        · subst u
          simpa only [NamedWorld.step, Function.update_self] using process_claim S rho i v o ih
        · simpa only [NamedWorld.step, Function.update_of_ne hvu] using carry

/-- No schedule assumptions: the original event index and actual pre-clock
store are produced by the fixed initial state and named event fold. -/
theorem completed_phase_origin (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V)
    (r : Round) (p : Phase) (root : Option (Block V))
    (h : phaseResult (cacheAtRound (NamedRun.stateBefore S rho i v).cache r) p = some root) :
    Origin S rho i v r p root (NamedRun.stateBefore S rho i v).st.core.F :=
  cache_lookup_claim _ _ (prefix_claim S rho i v) r p root h

/-- Ordinary ordering identifies each capture's actual local pre-clock
state with its strict time-filter read. No schedule-observation premise is used. -/
theorem completed_phase_origin_strict (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (hnodup : rho.events.Nodup)
    (i : Nat) (v : V) (r : Round) (p : Phase) (root : Option (Block V))
    (h : phaseResult (cacheAtRound (NamedRun.stateBefore S rho i v).cache r) p = some root) :
    (r = 0 ∧ root = none) ∨ ∃ (j : Nat) (t : Time),
      j < i ∧ rho.events[j]? = some (.tick v t) ∧ t = domain S.E S.hc r p ∧
      root = (freezeRoot S.E
        (NamedRun.stateBeforeTime S rho t v).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho t v).st.core.F S.hc.η_SG r
        (early S.E S.hc r p) (late S.E S.hc r p)).map
          (fun B => clipGrade B (NamedRun.stateBefore S rho i v).st.core.F) := by
  rcases completed_phase_origin S rho i v r p root h with hzero | ⟨j, t, hj, he, ht, hr⟩
  · exact Or.inl hzero
  · refine Or.inr ⟨j, t, hj, he, ht, ?_⟩
    simpa only [Proofs.NamedRuntime.tick_prefix_eq_strict S rho hsorted hnodup he] using hr

/-- A completed phase at an actual strict reader state comes from the
initial empty frame or a capture strictly before that read, with later clips
collapsed to this reader's actual finalized root. -/
theorem completed_phase_before_read (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (hnodup : rho.events.Nodup)
    (read : Time) (v : V) (r : Round) (p : Phase) (root : Option (Block V))
    (h : phaseResult (cacheAtRound (NamedRun.stateBeforeTime S rho read v).cache r) p = some root) :
    (r = 0 ∧ root = none) ∨ ∃ (j : Nat) (t : Time),
      rho.events[j]? = some (.tick v t) ∧ t < read ∧ t = domain S.E S.hc r p ∧
      root = (freezeRoot S.E
        (NamedRun.stateBeforeTime S rho t v).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho t v).st.core.F S.hc.η_SG r
        (early S.E S.hc r p) (late S.E S.hc r p)).map
          (fun B => clipGrade B (NamedRun.stateBeforeTime S rho read v).st.core.F) := by
  obtain ⟨n, hread, htime⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho hsorted read
  rw [hread] at h
  rcases completed_phase_origin_strict S rho hsorted hnodup n v r p root h with
    hzero | ⟨j, t, hj, he, ht, hr⟩
  · exact Or.inl hzero
  · refine Or.inr ⟨j, t, he, htime j (.tick v t) hj he, ht, ?_⟩
    simpa only [hread] using hr

#print axioms completed_phase_origin
#print axioms completed_phase_origin_strict
#print axioms completed_phase_before_read
end DecoupledConsensusModel.Proofs.NamedCacheProvenance

end
