module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.CacheProvenance
public import DecoupledConsensusProofs.Execution.HealthyLocalFacts
public import DecoupledConsensusInternal.Definitions.NamedJointOutage

@[expose] public section

/-!
# Forward cache provenance (row Q21, earlier tree)

`NamedCacheProvenance` reads a completed phase result backwards to its capture
tick. This file is the forward direction: once the round-`r` phase-`p` result is
completed in an honest node's cache, every later read of that node up to the
action time `a_r` returns the same result, clipped against that later read's
finalized root.

The clip is not cosmetic. Every tick and every delivery re-clips the whole cache
against the current `F`, so exact equality of the two reads is false in general;
the true invariant is equality up to clipping, which is also what the selection's
row Q21 states (`Q21_frame_persists_up_to_clip`).

The addressability window is the cache's two-frame window: `cacheAtRound c r` is
`c.current` at `r = c.round`, `c.next` at `r = c.round + 1`, and pending
otherwise, and every tick realigns the cache round to
`round_of (slotOf t)`. The bound used here is `t' ≤ a_r`, which keeps the clock
round at or below `r` and therefore keeps the round-`r` frame addressable.
-/

namespace DecoupledConsensusModel.Proofs.FrameForward
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Clipping algebra

Copies of the private helpers of `NamedCacheProvenance`; nothing new is proved
here. Promoting them and deleting this block is the natural next step. -/

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
private theorem clip_compatible (g F : Block V) : Block.compatible (clipGrade g F) F = true := by
  induction g with
  | genesis => simp [clipGrade, Block.compatible, Protocol.preceq_genesis]
  | node p s root gv gsv ats v ih =>
    simp only [clipGrade]
    split
    · assumption
    · exact ih

omit [Fintype V] in
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

omit [Fintype V] in
private theorem compatible_ancestors {A B C D : Block V}
    (hAB : Block.Preceq A B) (hCD : Block.Preceq C D)
    (hBD : Block.compatible B D = true) : Block.compatible A C = true := by
  simp only [Block.compatible, Bool.or_eq_true] at hBD
  rcases hBD with hBD | hDB
  · exact Block.compatible_of_preceq_common (Block.preceq_trans hAB hBD) hCD
  · exact Block.compatible_of_preceq_common hAB (Block.preceq_trans hCD hDB)

omit [Fintype V] in
private theorem clip_after_advance (B F G : Block V) (hFG : Block.Preceq F G) :
    clipGrade (clipGrade B F) G = clipGrade B G := by
  apply Block.preceq_antisymm
  · apply (retained_prefix B G _ (clip_compatible (clipGrade B F) G)).mpr
    exact Block.preceq_trans (clip_preceq (clipGrade B F) G) (clip_preceq B F)
  · apply (retained_prefix (clipGrade B F) G _ (clip_compatible B G)).mpr
    apply (retained_prefix B F _ ?_).mpr
    · exact clip_preceq B G
    · exact compatible_ancestors (Block.preceq_self _) hFG (clip_compatible B G)

omit [Fintype V] in
/-- Clipping twice against an advancing root is clipping once against the
later root. This is the only reason the forward statement is stated up to
clipping instead of as an equality. -/
private theorem clip_result_advance (F G : Block V) (hFG : Block.Preceq F G)
    (x : Option (Option (Block V))) : clipResult G (clipResult F x) = clipResult G x := by
  cases x with
  | none => rfl
  | some root =>
    cases root with
    | none => rfl
    | some B =>
      simp only [clipResult, Option.map_some]
      exact congrArg (fun C => some (some C)) (clip_after_advance B F G hFG)

/-! ## Cache algebra -/

omit [Fintype V] in
private theorem phase_clip_frame (F : Block V) (f : Frame V) (p : Phase) :
    phaseResult (clipFrame F f) p = clipResult F (phaseResult f p) := by
  cases p <;> rfl

omit [Fintype V] in
private theorem cacheAtRound_clip (F : Block V) (c : Cache V) (r : Round) :
    cacheAtRound (clipCache F c) r = clipFrame F (cacheAtRound c r) := by
  unfold cacheAtRound clipCache
  split_ifs <;> rfl

omit [Fintype V] in
private theorem phase_clip (F : Block V) (c : Cache V) (r : Round) (p : Phase) :
    phaseResult (cacheAtRound (clipCache F c) r) p =
      clipResult F (phaseResult (cacheAtRound c r) p) := by
  rw [cacheAtRound_clip, phase_clip_frame]

/-- `Round` is a reducible alias, but `omega` reads the type argument of `≤`
syntactically, so the two round comparisons are discharged at `Nat`. -/
private theorem round_succ_ne {a r : Nat} (h : a + 1 ≤ r) : ¬ r = a := by omega

private theorem round_gap {a q r : Nat} (hlow : a ≤ q) (hhigh : q ≤ r)
    (h1 : ¬ q = a) (h2 : ¬ q = a + 1) : ¬ r = a ∧ ¬ r = a + 1 := by omega

omit [DecidableEq V] [Fintype V] in
/-- Alignment to a round between the cache's own round and the queried round
never drops the queried frame. The two lost cases are alignment past the
queried round and a backwards clock; both are excluded here. -/
private theorem cacheAtRound_align (c : Cache V) (q r : Round)
    (hlow : c.round ≤ q) (hhigh : q ≤ r) :
    cacheAtRound (alignRound c q) r = cacheAtRound c r := by
  by_cases h1 : q = c.round
  · rw [show alignRound c q = c by unfold alignRound; rw [if_pos h1]]
  · by_cases h2 : q = c.round + 1
    · rw [show alignRound c q = ⟨q, c.next, pendingFrame⟩ by
        unfold alignRound; rw [if_neg h1, if_pos h2]]
      subst h2
      by_cases hr : r = c.round + 1
      · subst hr
        simp [cacheAtRound]
      · have h3 : ¬ r = c.round := round_succ_ne hhigh
        simp [cacheAtRound, hr, h3]
    · rw [show alignRound c q = ⟨q, pendingFrame, pendingFrame⟩ by
        unfold alignRound; rw [if_neg h1, if_neg h2]]
      obtain ⟨h3, h4⟩ := round_gap hlow hhigh h1 h2
      simp [cacheAtRound, h3, h4]

omit [DecidableEq V] [Fintype V] in
/-- Alignment to the queried round itself is always safe. -/
private theorem cacheAtRound_align_self (c : Cache V) (r : Round) :
    cacheAtRound (alignRound c r) r = cacheAtRound c r := by
  by_cases h1 : r = c.round
  · rw [show alignRound c r = c by unfold alignRound; rw [if_pos h1]]
  · by_cases h2 : r = c.round + 1
    · rw [show alignRound c r = ⟨r, c.next, pendingFrame⟩ by
        unfold alignRound; rw [if_neg h1, if_pos h2]]
      subst h2
      simp [cacheAtRound]
    · rw [show alignRound c r = ⟨r, pendingFrame, pendingFrame⟩ by
        unfold alignRound; rw [if_neg h1, if_neg h2]]
      simp [cacheAtRound, h1, h2]

private theorem complete_one_other (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) (t : Time) (p q : Phase) (f : Frame V) (h : q ≠ p) :
    phaseResult (completeOne E hc st r t p f) q = phaseResult f q := by
  unfold completeOne
  split
  · rfl
  · split
    · cases p <;> cases q <;> simp_all only [putPhase, phaseResult, ne_eq, not_true_eq_false]
    · rfl

/-- A completed result is never recalculated, so one completion pass leaves it
alone whatever the tick time is. -/
private theorem complete_one_some (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) (t : Time) (p q : Phase) (f : Frame V)
    (h : phaseResult f p ≠ none) :
    phaseResult (completeOne E hc st r t q f) p = phaseResult f p := by
  by_cases hpq : p = q
  · subst hpq
    unfold completeOne
    split
    · rfl
    · rename_i hnone
      exact absurd hnone h
  · exact complete_one_other E hc st r t q p f hpq

private theorem complete_frame_some (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) (t : Time) (p : Phase) (f : Frame V)
    (h : phaseResult f p ≠ none) :
    phaseResult (completeFrame E hc st r t f) p = phaseResult f p := by
  have h2 := complete_one_some E hc st r t p .g2 f h
  have h2' : phaseResult (completeOne E hc st r t .g2 f) p ≠ none := by
    rw [h2]; exact h
  have h1 := complete_one_some E hc st r t p .g1 _ h2'
  have h1' : phaseResult (completeOne E hc st r t .g1
      (completeOne E hc st r t .g2 f)) p ≠ none := by
    rw [h1, h2]; exact h
  have h0 := complete_one_some E hc st r t p .g0 _ h1'
  unfold completeFrame
  rw [h0, h1, h2]

/-- The completion pass of one tick writes the round-`r` phase-`p` slot only at
its own domain, and never over an already completed slot. -/
private theorem phase_completed_cache (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (c : Cache V) (t : Time) (r : Round) (p : Phase)
    (h : phaseResult (cacheAtRound c r) p ≠ none) :
    phaseResult (cacheAtRound ⟨c.round, completeFrame E hc st c.round t c.current,
        completeFrame E hc st (c.round + 1) t c.next⟩ r) p =
      phaseResult (cacheAtRound c r) p := by
  by_cases h1 : r = c.round
  · have e1 : cacheAtRound ⟨c.round, completeFrame E hc st c.round t c.current,
        completeFrame E hc st (c.round + 1) t c.next⟩ r =
        completeFrame E hc st c.round t c.current := by
      simp [cacheAtRound, h1]
    have e2 : cacheAtRound c r = c.current := by simp [cacheAtRound, h1]
    rw [e2] at h
    rw [e1, e2]
    exact complete_frame_some E hc st c.round t p c.current h
  · by_cases h2 : r = c.round + 1
    · have e1 : cacheAtRound ⟨c.round, completeFrame E hc st c.round t c.current,
          completeFrame E hc st (c.round + 1) t c.next⟩ r =
          completeFrame E hc st (c.round + 1) t c.next := by
        simp [cacheAtRound, h2]
      have e2 : cacheAtRound c r = c.next := by simp [cacheAtRound, h2]
      rw [e2] at h
      rw [e1, e2]
      exact complete_frame_some E hc st (c.round + 1) t p c.next h
    · have e1 : cacheAtRound ⟨c.round, completeFrame E hc st c.round t c.current,
          completeFrame E hc st (c.round + 1) t c.next⟩ r = pendingFrame := by
        simp [cacheAtRound, h1, h2]
      have e2 : cacheAtRound c r = pendingFrame := by simp [cacheAtRound, h1, h2]
      rw [e1, e2]

/-! ## The local clock round -/

/-- The round a tick at time `t` aligns the cache to. -/
private def clockRound (S : Setup V) (t : Time) : Round :=
  S.hc.round_of (S.E.slotOf t)

private theorem slotOf_le (E : Env V) {a b : Time} (h : a ≤ b) :
    E.slotOf a ≤ E.slotOf b := by
  have hpos : (0 : Time) < 4 * E.Δ :=
    Int.mul_pos (by decide) E.Δ_pos
  simp only [Env.slotOf, slotOfTime]
  rw [Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt hpos),
    Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt hpos)]
  exact Int.toNat_le_toNat (Int.ediv_le_ediv hpos h)

private theorem clockRound_le (S : Setup V) {a b : Time} (h : a ≤ b) :
    clockRound S a ≤ clockRound S b :=
  Nat.div_le_div_right (slotOf_le S.E h)


private theorem slotOf_zero (E : Env V) : E.slotOf (0 : Time) = 0 := by
  simp [Env.slotOf, slotOfTime]

/-- `6Δ < 4ΔR` for `R ≥ 2`. Stated at raw `Int` because `omega` refuses the
`Time` alias, and split into a scaling step because the product is not linear. -/
private theorem six_lt_four_mul {d k : Int} (hd : 0 < d) (hk : 2 ≤ k) :
    6 * d < 4 * d * k := by
  have h1 : (8 : Int) ≤ 4 * k := by omega
  have h2 : d * 8 ≤ d * (4 * k) := Int.mul_le_mul_of_nonneg_left h1 hd.le
  calc 6 * d < 8 * d := by omega
    _ = d * 8 := by ring
    _ ≤ d * (4 * k) := h2
    _ = 4 * d * k := by ring

/-- The round action is strictly inside its own round: `a_r = t_{rR} + 6Δ` and
the next opening is `t_{rR} + 4RΔ`, with `R ≥ 2`. -/
theorem a_lt_opening_succ (S : Setup V) (r : Round) :
    S.a r < opening S.E S.hc (r + 1) := by
  have hR : (2 : Time) ≤ ((S.hc.R : Nat) : Time) := by exact_mod_cast S.hc.R_ge_two
  have ha : S.a r = 4 * S.E.Δ * ((S.hc.opening_slot r : Nat) : Time) + 6 * S.E.Δ := rfl
  have ho : opening S.E S.hc (r + 1)
      = 4 * S.E.Δ * ((S.hc.opening_slot (r + 1) : Nat) : Time) := rfl
  have hcast : ((S.hc.opening_slot (r + 1) : Nat) : Time)
      = ((S.hc.opening_slot r : Nat) : Time) + ((S.hc.R : Nat) : Time) := by
    simp only [Protocol.HealConfig.opening_slot]
    push_cast
    ring
  rw [ha, ho, hcast]
  have hexp : 4 * S.E.Δ * (((S.hc.opening_slot r : Nat) : Time) + ((S.hc.R : Nat) : Time))
      = 4 * S.E.Δ * ((S.hc.opening_slot r : Nat) : Time)
        + 4 * S.E.Δ * ((S.hc.R : Nat) : Time) := by ring
  rw [hexp]
  exact Int.add_lt_add_left (six_lt_four_mul S.E.Δ_pos hR) _

private theorem zero_lt_six_mul {d : Int} (hd : 0 < d) : 0 * d < 6 * d := by omega

/-- Every phase domain of round `r` is at or before the round action. Public,
because `DomainIncluded` now bounds `b0` by the round opening and every consumer
has to recover `b0 ≤ S.a r` from it. -/
theorem domain_le_a (S : Setup V) (r : Round) (p : Phase) :
    domain S.E S.hc r p ≤ S.a r := by
  have hd : domain S.E S.hc r p
      = 4 * S.E.Δ * ((S.hc.opening_slot r : Nat) : Time) + p.domainOffset * S.E.Δ := rfl
  have ha : S.a r = 4 * S.E.Δ * ((S.hc.opening_slot r : Nat) : Time) + 6 * S.E.Δ := rfl
  rw [hd, ha]
  refine Int.add_le_add_left ?_ _
  refine Int.mul_le_mul_of_nonneg_right ?_ S.E.Δ_pos.le
  cases p <;> simp only [Phase.domainOffset] <;> norm_num

/-- The round opening is strictly before the round action: `a_r = opening + 6Δ`. -/
theorem opening_lt_a (S : Setup V) (r : Round) :
    domain S.E S.hc r .g1 < S.a r := by
  have hd : domain S.E S.hc r .g1
      = 4 * S.E.Δ * ((S.hc.opening_slot r : Nat) : Time) + 0 * S.E.Δ := rfl
  have ha : S.a r = 4 * S.E.Δ * ((S.hc.opening_slot r : Nat) : Time) + 6 * S.E.Δ := rfl
  rw [hd, ha]
  exact Int.add_lt_add_left (zero_lt_six_mul S.E.Δ_pos) _

/-- **The real addressability bound.** Every time strictly before the opening of
round `r + 1` has clock round at most `r`, so the round-`r` frame is still
addressable in the cache there. The bound `t ≤ a_r` used by the first version of
this file is the special case that covers only the first `6Δ` of each round;
`a_lt_opening_succ` recovers it. -/
private theorem clockRound_le_of_lt_opening (S : Setup V) {t : Time} {r : Round}
    (ht : t < opening S.E S.hc (r + 1)) : clockRound S t ≤ r := by
  have hR : 0 < S.hc.R := lt_of_lt_of_le (by decide) S.hc.R_ge_two
  have hop : opening S.E S.hc (r + 1)
      = Protocol.proposal_time S.E (S.hc.opening_slot (r + 1)) := rfl
  rw [hop] at ht
  have hslot : S.E.slotOf t < S.hc.opening_slot (r + 1) := by
    by_cases h0 : (0 : Time) ≤ t
    · by_contra hnot
      have hs : S.hc.opening_slot (r + 1) ≤ S.E.slotOf t := Nat.not_lt.mp hnot
      exact absurd (le_trans (Protocol.proposal_time_mono S.E hs)
        (Protocol.proposal_time_slotOf_le S.E h0)) (not_le.mpr ht)
    · have hneg : t < 0 := not_le.mp h0
      have hz : S.E.slotOf t = 0 :=
        Nat.le_zero.mp (le_trans (slotOf_le S.E hneg.le) (le_of_eq (slotOf_zero S.E)))
      rw [hz]
      exact Nat.mul_pos (Nat.succ_pos r) hR
  have hdiv : S.E.slotOf t / S.hc.R < r + 1 := by
    refine (Nat.div_lt_iff_lt_mul hR).mpr ?_
    simpa [Protocol.HealConfig.opening_slot] using hslot
  exact Nat.lt_succ_iff.mp hdiv

/-! ## The cache round is the round of an earlier tick of the same node -/

private theorem cache_round_witness (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V) :
    (NamedRun.stateBefore S rho i v).cache.round = 0 ∨
      ∃ (k : Nat) (tau : Time), k < i ∧ rho.events[k]? = some (.tick v tau) ∧
        (NamedRun.stateBefore S rho i v).cache.round = clockRound S tau := by
  induction i with
  | zero => exact Or.inl rfl
  | succ i ih =>
    have carry : (NamedRun.stateBefore S rho i v).cache.round = 0 ∨
        ∃ (k : Nat) (tau : Time), k < i + 1 ∧ rho.events[k]? = some (.tick v tau) ∧
          (NamedRun.stateBefore S rho i v).cache.round = clockRound S tau := by
      rcases ih with h | ⟨k, tau, hk, he, hr⟩
      · exact Or.inl h
      · exact Or.inr ⟨k, tau, Nat.lt_succ_of_lt hk, he, hr⟩
    cases he : rho.events[i]? with
    | none =>
      rw [Proofs.NamedRuntime.stateBefore_succ]
      simpa only [he, Option.toList_none, List.foldl_nil] using carry
    | some e =>
      cases e with
      | tick u t =>
        by_cases hvu : v = u
        · subst hvu
          rw [Proofs.NamedRuntime.stateBefore_tick S rho he]
          exact Or.inr ⟨i, t, Nat.lt_succ_self i, he,
            NamedNode.tick_cache_round S v _ t⟩
        · rw [Proofs.NamedRuntime.stateBefore_other S rho he v hvu]
          exact carry
      | deliver u o t =>
        by_cases hvu : v = u
        · subst hvu
          rw [Proofs.NamedRuntime.stateBefore_deliver S rho he]
          simpa only [NamedNode.process_cache_round] using carry
        · rw [Proofs.NamedRuntime.stateBefore_other S rho he v hvu]
          exact carry

omit [DecidableEq V] [Fintype V] in
private theorem time_le_of_key_le {e f : NamedEvent V} (h : e.key ≤ f.key) :
    e.time ≤ f.time := by
  rcases Prod.Lex.le_iff.mp h with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

omit [DecidableEq V] [Fintype V] in
private theorem time_le_of_index_le (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    {k i : Nat} {e f : NamedEvent V} (hki : k < i)
    (hk : rho.events[k]? = some e) (hi : rho.events[i]? = some f) : e.time ≤ f.time := by
  obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  have hp := (List.pairwise_iff_getElem.mp hsorted) k i hkl hil hki
  rw [hke, hie] at hp
  exact time_le_of_key_le hp

/-- No node's cache round runs ahead of the clock round of its own next tick. -/
private theorem cache_round_le_tick (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    {i : Nat} {v : V} {tau : Time} (he : rho.events[i]? = some (.tick v tau)) :
    (NamedRun.stateBefore S rho i v).cache.round ≤ clockRound S tau := by
  rcases cache_round_witness S rho i v with h | ⟨k, tau0, hk, hke, hr⟩
  · rw [h]; exact Nat.zero_le _
  · rw [hr]
    exact clockRound_le S (time_le_of_index_le rho hsorted hk hke he)

/-! ## The forward step over event indices -/

private theorem slot_persists_index (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (v : V) (r : Round) (p : Phase) (n : Nat) (root : Option (Block V))
    (hbase : phaseResult (cacheAtRound (NamedRun.stateBefore S rho n v).cache r) p =
      some root) :
    ∀ m, n ≤ m →
      (∀ j tau, n ≤ j → j < m → rho.events[j]? = some (.tick v tau) →
        clockRound S tau ≤ r) →
      phaseResult (cacheAtRound (NamedRun.stateBefore S rho m v).cache r) p =
        clipResult (NamedRun.stateBefore S rho m v).st.core.F (some root) := by
  intro m hnm
  induction m, hnm using Nat.le_induction with
  | base =>
    intro _
    have hclip := (Proofs.NamedRuntime.stateBefore_invariants S rho n v).2.2
    have key : phaseResult (cacheAtRound (NamedRun.stateBefore S rho n v).cache r) p =
        clipResult (NamedRun.stateBefore S rho n v).st.core.F
          (phaseResult (cacheAtRound (NamedRun.stateBefore S rho n v).cache r) p) := by
      conv_lhs => rw [← hclip]
      exact phase_clip _ _ _ _
    rw [hbase] at key
    rw [hbase]
    exact key
  | succ m hnm ih =>
    intro hwin
    have ihm := ih (fun j tau hj hjm hget => hwin j tau hj (Nat.lt_succ_of_lt hjm) hget)
    have hsome : phaseResult (cacheAtRound (NamedRun.stateBefore S rho m v).cache r) p
        ≠ none := by
      rw [ihm]
      simp only [clipResult, Option.map_some, ne_eq, reduceCtorEq, not_false_eq_true]
    cases he : rho.events[m]? with
    | none =>
      rw [Proofs.NamedRuntime.stateBefore_succ]
      simpa only [he, Option.toList_none, List.foldl_nil] using ihm
    | some e =>
      cases e with
      | tick u t =>
        by_cases hvu : v = u
        · subst hvu
          have hround : (NamedRun.stateBefore S rho m v).cache.round ≤ clockRound S t :=
            cache_round_le_tick S rho hsorted he
          have hclock : clockRound S t ≤ r :=
            hwin m t hnm (Nat.lt_succ_self m) he
          rw [Proofs.NamedRuntime.stateBefore_tick S rho he]
          set nd := NamedRun.stateBefore S rho m v with hnd
          have hmono : Block.Preceq nd.st.core.F
              (NamedNode.tick S v nd t).1.st.core.F :=
            NamedFinalityMonotone.node_tick_F S v nd t
          rw [NamedNode.tick_cache_eq, phase_clip]
          have hprep : phaseResult (cacheAtRound
              (onPhaseTick S.E S.hc nd.st.core.toHealing t nd.cache) r) p =
            clipResult nd.st.core.F
              (phaseResult (cacheAtRound nd.cache r) p) := by
            unfold onPhaseTick
            set al := alignRound nd.cache (S.hc.round_of (S.E.slotOf t)) with hal
            have halign : cacheAtRound al r = cacheAtRound nd.cache r :=
              cacheAtRound_align nd.cache _ r hround hclock
            have hsome' : phaseResult (cacheAtRound al r) p ≠ none := by
              rw [halign]; exact hsome
            change phaseResult (cacheAtRound (clipCache nd.st.core.F
              ⟨al.round, completeFrame S.E S.hc nd.st.core.toHealing al.round t al.current,
                completeFrame S.E S.hc nd.st.core.toHealing (al.round + 1) t al.next⟩) r) p = _
            rw [phase_clip, phase_completed_cache S.E S.hc nd.st.core.toHealing al t r p hsome',
              halign]
          rw [hprep, ihm, clip_result_advance _ _ (Block.preceq_self _),
            clip_result_advance _ _ hmono]
        · rw [Proofs.NamedRuntime.stateBefore_other S rho he v hvu]
          exact ihm
      | deliver u o t =>
        by_cases hvu : v = u
        · subst hvu
          rw [Proofs.NamedRuntime.stateBefore_deliver S rho he]
          set nd := NamedRun.stateBefore S rho m v with hnd
          have hmono : Block.Preceq nd.st.core.F
              (NamedNode.process S nd o).st.core.F :=
            NamedFinalityMonotone.node_process_F S nd o
          rw [NamedNode.process_cache_eq, phase_clip, ihm,
            clip_result_advance _ _ hmono]
        · rw [Proofs.NamedRuntime.stateBefore_other S rho he v hvu]
          exact ihm

/-! ## Strict reads by time -/

private def beforeIdx (rho : NamedRun V) (t : Time) : Nat :=
  (rho.events.filter (fun e => decide (e.time < t))).length

omit [DecidableEq V] [Fintype V] in
private theorem strict_filter_eq_take (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (cut : Time) :
    rho.events.filter (fun e => decide (e.time < cut)) =
      rho.events.take (beforeIdx rho cut) := by
  have hdown : ∀ e f : NamedEvent V, e.key ≤ f.key →
      decide (f.time < cut) = true → decide (e.time < cut) = true := by
    intro e f hkey hf
    simp only [decide_eq_true_eq] at hf ⊢
    exact (time_le_of_key_le hkey).trans_lt hf
  refine List.prefix_iff_eq_take.mp ?_
  rw [Proofs.Bridges.filter_eq_takeWhile_of_pairwise hdown _ hsorted]
  exact List.takeWhile_prefix _

private theorem stateBeforeTime_eq_idx (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (t : Time) :
    NamedRun.stateBeforeTime S rho t = NamedRun.stateBefore S rho (beforeIdx rho t) :=
  congrArg (fun events => events.foldl (NamedWorld.step S) NamedWorld.init)
    (strict_filter_eq_take rho hsorted t)

omit [DecidableEq V] [Fintype V] in
private theorem beforeIdx_mono (rho : NamedRun V) {t t' : Time} (h : t ≤ t') :
    beforeIdx rho t ≤ beforeIdx rho t' := by
  have hrw : rho.events.filter (fun e => decide (e.time < t)) =
      (rho.events.filter (fun e => decide (e.time < t'))).filter
        (fun e => decide (e.time < t)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro e _
    by_cases hc : e.time < t
    · have hc' : e.time < t' := lt_of_lt_of_le hc h
      simp [hc, hc']
    · simp [hc]
  unfold beforeIdx
  rw [hrw]
  exact List.length_filter_le _ _

omit [DecidableEq V] [Fintype V] in
private theorem time_lt_of_lt_beforeIdx (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (t : Time)
    {j : Nat} {e : NamedEvent V} (hj : j < beforeIdx rho t)
    (hget : rho.events[j]? = some e) : e.time < t := by
  have hm : e ∈ rho.events.filter (fun x => decide (x.time < t)) := by
    rw [strict_filter_eq_take rho hsorted t]
    exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj]; exact hget)
  simpa only [decide_eq_true_eq] using (List.mem_filter.mp hm).2

/-! ## The forward statement -/

/-- **Forward cache provenance.** A round-`r` phase-`p` result already completed
in `v`'s cache at the strict read of `t` is still there at every strict read up
to the action time `a_r`, changed only by clipping against the later finalized
root. No honesty, fault bound or delivery premise is used; only the event order.

This is the earlier-tree instance of the selection's row Q21
(`Q21_frame_persists_up_to_clip`, `PhaseGradeQueries.lean:307`), one phase at a
time and with the selection's own addressability bound, here at or before
`opening (r + 1)` since only ticks strictly before `t'` are read. -/
theorem frame_phase_persists_in_round (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (v : V) (r : Round) (p : Phase) (t t' : Time)
    (htt' : t ≤ t') (hclip : t' ≤ opening S.E S.hc (r + 1)) (root : Option (Block V))
    (hbase : phaseResult (DecoupledConsensusModel.Protocol.readFrame
        (NamedRun.stateBeforeTime S rho t v).cache
        (NamedRun.stateBeforeTime S rho t v).st.core.toHealing r) p = some root) :
    phaseResult (DecoupledConsensusModel.Protocol.readFrame
        (NamedRun.stateBeforeTime S rho t' v).cache
        (NamedRun.stateBeforeTime S rho t' v).st.core.toHealing r) p =
      clipResult (NamedRun.stateBeforeTime S rho t' v).st.core.F (some root) := by
  have hsorted := core.sorted
  have hraw : ∀ (u : Time), phaseResult (DecoupledConsensusModel.Protocol.readFrame
      (NamedRun.stateBeforeTime S rho u v).cache
      (NamedRun.stateBeforeTime S rho u v).st.core.toHealing r) p =
    phaseResult (cacheAtRound (NamedRun.stateBeforeTime S rho u v).cache r) p := by
    intro u
    have hclipped := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho u v).2.2
    change phaseResult (clipFrame (NamedRun.stateBeforeTime S rho u v).st.core.F
      (cacheAtRound (NamedRun.stateBeforeTime S rho u v).cache r)) p = _
    rw [← cacheAtRound_clip, hclipped]
  rw [hraw] at hbase ⊢
  rw [stateBeforeTime_eq_idx S rho hsorted t] at hbase
  rw [stateBeforeTime_eq_idx S rho hsorted t']
  refine slot_persists_index S rho hsorted v r p _ root hbase _
    (beforeIdx_mono rho htt') ?_
  intro j tau _ hjm hget
  have hlt : NamedEvent.time (NamedEvent.tick v tau) < t' :=
    time_lt_of_lt_beforeIdx rho hsorted t' hjm hget
  change tau < t' at hlt
  exact clockRound_le_of_lt_opening S (lt_of_lt_of_le hlt hclip)

/-- **Old form, as a corollary.** `a_r` is strictly inside round `r`, so the
action-time bound is the special case of the clock-round bound. -/
theorem frame_phase_persists (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (v : V) (r : Round) (p : Phase) (t t' : Time)
    (htt' : t ≤ t') (hclip : t' ≤ S.a r) (root : Option (Block V))
    (hbase : phaseResult (DecoupledConsensusModel.Protocol.readFrame
        (NamedRun.stateBeforeTime S rho t v).cache
        (NamedRun.stateBeforeTime S rho t v).st.core.toHealing r) p = some root) :
    phaseResult (DecoupledConsensusModel.Protocol.readFrame
        (NamedRun.stateBeforeTime S rho t' v).cache
        (NamedRun.stateBeforeTime S rho t' v).st.core.toHealing r) p =
      clipResult (NamedRun.stateBeforeTime S rho t' v).st.core.F (some root) :=
  frame_phase_persists_in_round S rho core v r p t t' htt'
    (le_of_lt (lt_of_le_of_lt hclip (a_lt_opening_succ S r))) root hbase



/-! ## The checkpoint read -/

/-- The action-time checkpoint reads the same saved slot as the strict read at
`a_r`. The confirmation staging only sets the clock and runs the cache
preparation, which cannot complete an already completed slot and clips against
the same `F`. -/
theorem frame_phase_checkpoint_eq (S : Setup V) (rho : NamedRun V)
    (v : V) (r : Round) (p : Phase) (root : Option (Block V))
    (hbase : phaseResult (DecoupledConsensusModel.Protocol.readFrame
        (NamedRun.stateBeforeTime S rho (S.a r) v).cache
        (NamedRun.stateBeforeTime S rho (S.a r) v).st.core.toHealing r) p = some root) :
    phaseResult (DecoupledConsensusModel.Protocol.readFrame (checkpoint S rho v r).cache
      (checkpoint S rho v r).st.core.toHealing r) p = some root := by
  set before := NamedRun.stateBeforeTime S rho (S.a r) v with hbefore
  have hclipped := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).2.2
  have hraw : phaseResult (cacheAtRound before.cache r) p = some root := by
    rw [← hbase]
    change _ = phaseResult (clipFrame before.st.core.F (cacheAtRound before.cache r)) p
    rw [← cacheAtRound_clip, hclipped]
  have hsome : phaseResult (cacheAtRound before.cache r) p ≠ none := by
    rw [hraw]; exact Option.some_ne_none _
  have hprep : phaseResult (cacheAtRound (preparedCache S before (S.a r)) r) p =
      clipResult before.st.core.F (phaseResult (cacheAtRound before.cache r) p) := by
    unfold preparedCache NamedActionReads.preparedCache onPhaseTick
    rw [Proofs.HealingLemmas.round_of_slotOf_a S r]
    set al := alignRound before.cache r with hal
    have halign : cacheAtRound al r = cacheAtRound before.cache r :=
      cacheAtRound_align_self before.cache r
    have hsome' : phaseResult (cacheAtRound al r) p ≠ none := by
      rw [halign]; exact hsome
    change phaseResult (cacheAtRound (clipCache before.st.core.F
      ⟨al.round, completeFrame S.E S.hc before.st.core.toHealing al.round (S.a r) al.current,
        completeFrame S.E S.hc before.st.core.toHealing (al.round + 1) (S.a r) al.next⟩) r) p = _
    rw [phase_clip,
      phase_completed_cache S.E S.hc before.st.core.toHealing al (S.a r) r p hsome', halign]
  have key : phaseResult (cacheAtRound before.cache r) p =
      clipResult before.st.core.F (phaseResult (cacheAtRound before.cache r) p) := by
    conv_lhs => rw [← hclipped]
    exact phase_clip _ _ _ _
  rw [hraw] at key
  change phaseResult (clipFrame before.st.core.F
    (cacheAtRound (preparedCache S before (S.a r)) r)) p = some root
  rw [phase_clip_frame, hprep, hraw, clip_result_advance _ _ (Block.preceq_self _)]
  exact key.symm

/-- **Checkpoint corollary.** A G2 result of round `r` completed at any strict
read between its domain tick and the action time is the one the round-`r`
checkpoint reads, clipped against the checkpoint's finalized root. -/
theorem frame_g2_at_checkpoint (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (v : V) (r : Round) (t : Time)
    (ht : t ≤ S.a r) (root : Option (Block V))
    (hbase : (DecoupledConsensusModel.Protocol.readFrame
        (NamedRun.stateBeforeTime S rho t v).cache
        (NamedRun.stateBeforeTime S rho t v).st.core.toHealing r).g2 = some root) :
    (DecoupledConsensusModel.Protocol.readFrame (checkpoint S rho v r).cache
        (checkpoint S rho v r).st.core.toHealing r).g2 =
      clipResult (NamedRun.stateBeforeTime S rho (S.a r) v).st.core.F (some root) := by
  have hstrict := frame_phase_persists S rho core v r .g2 t (S.a r) ht le_rfl root hbase
  have hcases : ∃ x, clipResult (NamedRun.stateBeforeTime S rho (S.a r) v).st.core.F
      (some root) = some x := by
    cases root with
    | none => exact ⟨none, rfl⟩
    | some B => exact ⟨_, rfl⟩
  obtain ⟨x, hx⟩ := hcases
  rw [hx] at hstrict ⊢
  exact frame_phase_checkpoint_eq S rho v r .g2 x hstrict

#print axioms opening_lt_a
#print axioms a_lt_opening_succ
#print axioms frame_phase_persists_in_round
#print axioms frame_phase_persists
#print axioms frame_phase_checkpoint_eq
#print axioms frame_g2_at_checkpoint

end DecoupledConsensusModel.Proofs.FrameForward

end
