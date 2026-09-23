module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.FrameForward

@[expose] public section

/-!
# Frame completion at the domain tick (row Q22, earlier tree)

`FrameForward` is the persistence half: a slot that is already `some` at one
strict read is still there, up to clipping, at every later strict read up to
`a_r`. This file is the completion half: the slot actually becomes `some` at its
own domain tick, so every strict read after that tick and up to `a_r` returns a
completed result, and the result is the one the domain tick computed.

The value is read back through `NamedCacheProvenance.completed_phase_before_read`
rather than carried forward by the induction. That backward row already names the
capture tick's store, so the only thing the forward walk has to carry is
"the slot is not `none`", which needs no clipping algebra at all.

Two facts drive the completion.

* `domain E hc r p` is a public time for `0 < r`: it is `(4rR + k)Δ` with
  `k ∈ {1, 0, -1}`, so an honest node ticks there whenever the run reaches it.
* The domain tick's own clock round addresses round `r`. The G0 and G1 domains
  are inside slot `rR`, so the aligned cache round is `r` and the `current`
  frame is the round-`r` frame. The G2 domain is one `Δ` *before* slot `rR`, so
  the aligned cache round is `r - 1` and the round-`r` frame is `next`. Either
  way `completeFrame` runs on the round-`r` frame with the matching label.
-/

namespace DecoupledConsensusModel.Proofs.FrameCompleted
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Round arithmetic

`Round` and `Slot` are `Nat` abbreviations, but `omega` reads the type argument
of `≤` and `/` syntactically, so every round computation is stated at `Nat` and
applied to round terms. -/

private theorem nat_mul_div_self (R k : Nat) (hR : 0 < R) : (k * R) / R = k := by
  rw [Nat.mul_comm]
  exact Nat.mul_div_cancel_left k hR

private theorem nat_pred_mul_div (R k : Nat) (hR : 0 < R) : ((k + 1) * R - 1) / R = k := by
  have h1 : (k + 1) * R - 1 = (R - 1) + k * R := by
    have h2 : (k + 1) * R = k * R + R := by ring
    omega
  rw [h1, Nat.add_mul_div_right _ _ hR, Nat.div_eq_of_lt (by omega), Nat.zero_add]

private theorem nat_succ_ne_self {a r : Nat} (h : r = a + 1) : ¬ r = a := by omega

/-- `Round` is a reducible alias, but `omega` reads the type argument of `≤`
syntactically, so the two round comparisons are discharged at `Nat`. -/
private theorem round_succ_ne {a r : Nat} (h : a + 1 ≤ r) : ¬ r = a := by omega

private theorem round_gap {a q r : Nat} (hlow : a ≤ q) (hhigh : q ≤ r)
    (h1 : ¬ q = a) (h2 : ¬ q = a + 1) : ¬ r = a ∧ ¬ r = a + 1 := by omega

private theorem healR_pos (S : Setup V) : 0 < S.hc.R :=
  Nat.lt_of_lt_of_le (by decide) S.hc.R_ge_two

private theorem nat_one_le_four_mul {x : Nat} (h : 1 ≤ x) : 1 ≤ 4 * x := by omega

/-- `Time` is a reducible alias of `Int`, and `omega` reads the type argument of
`<` syntactically, so every `Δ` comparison is stated at `Int` and applied. -/
private theorem delta_lt_four {d : Int} (hd : 0 < d) : d < 4 * d := by omega

private theorem zero_lt_four_delta {d : Int} (hd : 0 < d) : (0 : Int) < 4 * d := by omega

private theorem three_delta_nonneg {d : Int} (hd : 0 < d) : (0 : Int) ≤ 3 * d := by omega

private theorem three_delta_lt_four {d : Int} (hd : 0 < d) : 3 * d < 4 * d := by omega


private theorem opening_slot_pos (S : Setup V) {r : Round} (hr : 0 < r) :
    0 < S.hc.opening_slot r :=
  Nat.mul_pos hr (healR_pos S)

/-! ## The domain instants -/

private theorem opening_time (S : Setup V) (r : Round) :
    opening S.E S.hc r = 4 * S.E.Δ * ((S.hc.opening_slot r : Nat) : Time) := rfl

private theorem domain_time (S : Setup V) (r : Round) (p : Phase) :
    domain S.E S.hc r p =
      4 * S.E.Δ * ((S.hc.opening_slot r : Nat) : Time) + p.domainOffset * S.E.Δ := by
  unfold domain
  rw [opening_time]

/-- Every phase domain of a positive round is a public time: `(4rR + k)Δ` with
`k ∈ {1, 0, -1}`, and `4rR ≥ 1` for `0 < r`. -/
private theorem publicTime_domain (S : Setup V) {r : Round} (hr : 0 < r) (p : Phase) :
    PublicTime S (domain S.E S.hc r p) := by
  have hos : 1 ≤ S.hc.opening_slot r := opening_slot_pos S hr
  have hd := domain_time S r p
  cases p with
  | g0 =>
    refine ⟨4 * S.hc.opening_slot r + 1, ?_⟩
    rw [hd]
    simp only [Phase.domainOffset]
    push_cast
    ring
  | g1 =>
    refine ⟨4 * S.hc.opening_slot r, ?_⟩
    rw [hd]
    simp only [Phase.domainOffset]
    push_cast
    ring
  | g2 =>
    refine ⟨4 * S.hc.opening_slot r - 1, ?_⟩
    have h1 : 1 ≤ 4 * S.hc.opening_slot r := nat_one_le_four_mul hos
    have hcast : ((4 * S.hc.opening_slot r - 1 : Nat) : Time)
        = 4 * ((S.hc.opening_slot r : Nat) : Time) - 1 := by
      rw [Nat.cast_sub h1]
      push_cast
      ring
    rw [hd, hcast]
    simp only [Phase.domainOffset]
    ring

private theorem domain_nonneg (S : Setup V) {r : Round} (hr : 0 < r) (p : Phase) :
    (0 : Time) ≤ domain S.E S.hc r p := by
  obtain ⟨k, hk⟩ := publicTime_domain S hr p
  rw [hk]
  exact Int.mul_nonneg (Int.natCast_nonneg k) S.E.Δ_pos.le




/-! ## The clock round of a domain tick -/

/-- The round a tick at time `t` aligns the cache to. -/
private def clockRound (S : Setup V) (t : Time) : Round :=
  S.hc.round_of (S.E.slotOf t)

private theorem slotOf_domain_g0 (S : Setup V) (r : Round) :
    S.E.slotOf (domain S.E S.hc r .g0) = S.hc.opening_slot r := by
  have hd : domain S.E S.hc r .g0
      = 4 * S.E.Δ * ((S.hc.opening_slot r : Nat) : Time) + S.E.Δ := by
    rw [domain_time]
    simp only [Phase.domainOffset]
    ring
  unfold Env.slotOf
  rw [hd]
  exact Proofs.Optimistic.slotOfTime_add S.E.Δ S.E.Δ_pos _ _ S.E.Δ_pos.le
    (delta_lt_four S.E.Δ_pos)

private theorem slotOf_domain_g1 (S : Setup V) (r : Round) :
    S.E.slotOf (domain S.E S.hc r .g1) = S.hc.opening_slot r := by
  have hd : domain S.E S.hc r .g1
      = 4 * S.E.Δ * ((S.hc.opening_slot r : Nat) : Time) + 0 := by
    rw [domain_time]
    simp only [Phase.domainOffset]
    ring
  unfold Env.slotOf
  rw [hd]
  exact Proofs.Optimistic.slotOfTime_add S.E.Δ S.E.Δ_pos _ _ le_rfl
    (zero_lt_four_delta S.E.Δ_pos)

/-- The G2 domain of round `r` is `t_{rR} − Δ`, the last `Δ` of slot `rR − 1`. -/
private theorem slotOf_domain_g2 (S : Setup V) {r : Round} (hr : 0 < r) :
    S.E.slotOf (domain S.E S.hc r .g2) = S.hc.opening_slot r - 1 := by
  have hos : 1 ≤ S.hc.opening_slot r := opening_slot_pos S hr
  have hcast : ((S.hc.opening_slot r - 1 : Nat) : Time)
      = ((S.hc.opening_slot r : Nat) : Time) - 1 := by
    rw [Nat.cast_sub hos]
    norm_num
  have hd : domain S.E S.hc r .g2
      = 4 * S.E.Δ * (((S.hc.opening_slot r - 1 : Nat)) : Time) + 3 * S.E.Δ := by
    rw [domain_time, hcast]
    simp only [Phase.domainOffset]
    ring
  unfold Env.slotOf
  rw [hd]
  exact Proofs.Optimistic.slotOfTime_add S.E.Δ S.E.Δ_pos _ _
    (three_delta_nonneg S.E.Δ_pos) (three_delta_lt_four S.E.Δ_pos)

private theorem clockRound_domain_g0 (S : Setup V) (r : Round) :
    clockRound S (domain S.E S.hc r .g0) = r := by
  unfold clockRound
  rw [slotOf_domain_g0]
  simp only [Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
  exact nat_mul_div_self S.hc.R r (healR_pos S)

private theorem clockRound_domain_g1 (S : Setup V) (r : Round) :
    clockRound S (domain S.E S.hc r .g1) = r := by
  unfold clockRound
  rw [slotOf_domain_g1]
  simp only [Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
  exact nat_mul_div_self S.hc.R r (healR_pos S)

private theorem clockRound_domain_g2 (S : Setup V) {r : Round} (hr : 0 < r) :
    clockRound S (domain S.E S.hc r .g2) + 1 = r := by
  unfold clockRound
  rw [slotOf_domain_g2 S hr]
  simp only [Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
  cases r with
  | zero => exact absurd hr (Nat.lt_irrefl 0)
  | succ k => rw [nat_pred_mul_div S.hc.R k (healR_pos S)]

/-- The round-`r` frame is addressable in the cache the domain tick aligns to:
`r` itself for G0 and G1, and `r − 1 + 1` for G2. -/
private theorem domain_addressable (S : Setup V) {r : Round} (hr : 0 < r) (p : Phase)
    (c : Cache V) (hc : c.round = clockRound S (domain S.E S.hc r p)) :
    r = c.round ∨ r = c.round + 1 := by
  cases p with
  | g0 => exact Or.inl (by rw [hc, clockRound_domain_g0])
  | g1 => exact Or.inl (by rw [hc, clockRound_domain_g1])
  | g2 => exact Or.inr (by rw [hc, clockRound_domain_g2 S hr])

/-! ## Cache algebra

Copies of the private helpers of `FrameForward` and `NamedCacheProvenance`; the
clipping algebra is not needed here, because only "the slot is not `none`" is
carried forward. -/

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

omit [Fintype V] in
/-- Clipping never erases a completed slot; it only shortens the saved root. -/
private theorem clipResult_ne_none (F : Block V) (x : Option (Option (Block V)))
    (h : x ≠ none) : clipResult F x ≠ none := by
  cases x with
  | none => exact absurd rfl h
  | some y => simp only [clipResult, Option.map_some, ne_eq, reduceCtorEq, not_false_eq_true]

omit [DecidableEq V] [Fintype V] in
private theorem alignRound_round (c : Cache V) (q : Round) : (alignRound c q).round = q := by
  unfold alignRound
  split_ifs with h
  · exact h.symm
  · rfl
  · rfl

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

/-! ## One completion pass at the domain closes the slot -/

private theorem complete_one_domain_some (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) (t : Time) (p : Phase) (f : Frame V)
    (ht : t = domain E hc r p) :
    phaseResult (completeOne E hc st r t p f) p ≠ none := by
  by_cases hf : phaseResult f p = none
  · have he : completeOne E hc st r t p f
        = putPhase f p (freezeRoot E st.gradeView st.F hc.η_SG r
            (early E hc r p) (late E hc r p)) := by
      unfold completeOne
      rw [hf]
      exact if_pos ht
    rw [he]
    cases p <;> simp [putPhase, phaseResult]
  · rw [complete_one_some E hc st r t p p f hf]
    exact hf

/-- **The domain tick closes its own slot.** Whatever the frame held before,
after the round-`r` completion pass at time `domain r p` the phase-`p` slot is
`some`: either it was already completed, or `completeOne` writes the freeze. -/
private theorem complete_frame_domain_some (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) (t : Time) (p : Phase) (f : Frame V)
    (ht : t = domain E hc r p) :
    phaseResult (completeFrame E hc st r t f) p ≠ none := by
  unfold completeFrame
  cases p with
  | g0 => exact complete_one_domain_some E hc st r t .g0 _ ht
  | g1 =>
    rw [complete_one_other E hc st r t .g0 .g1 _ (by decide)]
    exact complete_one_domain_some E hc st r t .g1 _ ht
  | g2 =>
    rw [complete_one_other E hc st r t .g0 .g2 _ (by decide),
      complete_one_other E hc st r t .g1 .g2 _ (by decide)]
    exact complete_one_domain_some E hc st r t .g2 _ ht

/-- The same statement at the cache level, for a cache whose round addresses
round `r` (its own round, or one less). -/
private theorem phase_domain_cache (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (c : Cache V) (t : Time) (r : Round) (p : Phase)
    (ht : t = domain E hc r p) (haddr : r = c.round ∨ r = c.round + 1) :
    phaseResult (cacheAtRound ⟨c.round, completeFrame E hc st c.round t c.current,
        completeFrame E hc st (c.round + 1) t c.next⟩ r) p ≠ none := by
  rcases haddr with rfl | h2
  · have e1 : cacheAtRound (⟨c.round, completeFrame E hc st c.round t c.current,
        completeFrame E hc st (c.round + 1) t c.next⟩ : Cache V) c.round =
        completeFrame E hc st c.round t c.current := by
      simp [cacheAtRound]
    rw [e1]
    exact complete_frame_domain_some E hc st c.round t p c.current ht
  · have hne : ¬ r = c.round := nat_succ_ne_self h2
    have e1 : cacheAtRound (⟨c.round, completeFrame E hc st c.round t c.current,
        completeFrame E hc st (c.round + 1) t c.next⟩ : Cache V) r =
        completeFrame E hc st (c.round + 1) t c.next := by
      simp only [cacheAtRound, if_neg hne, if_pos h2]
    rw [e1, ← h2]
    exact complete_frame_domain_some E hc st r t p c.next ht

/-! ## The local clock is monotone -/

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

/-- **The real addressability bound.** Local copy of
`FrameForward.clockRound_le_of_lt_opening` over this file's own `clockRound`. -/
private theorem clockRound_le_of_lt_opening (S : Setup V) {t : Time} {r : Round}
    (ht : t < opening S.E S.hc (r + 1)) : clockRound S t ≤ r := by
  have hR : 0 < S.hc.R := healR_pos S
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

/-! ## The forward step over event indices

Only "the slot is not `none`" is carried. The value is recovered afterwards from
the backward row `NamedCacheProvenance.completed_phase_before_read`. -/

private theorem slot_some_index (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (v : V) (r : Round) (p : Phase) (n : Nat)
    (hbase : phaseResult (cacheAtRound (NamedRun.stateBefore S rho n v).cache r) p ≠ none) :
    ∀ m, n ≤ m →
      (∀ j tau, n ≤ j → j < m → rho.events[j]? = some (.tick v tau) →
        clockRound S tau ≤ r) →
      phaseResult (cacheAtRound (NamedRun.stateBefore S rho m v).cache r) p ≠ none := by
  intro m hnm
  induction m, hnm using Nat.le_induction with
  | base => intro _; exact hbase
  | succ m hnm ih =>
    intro hwin
    have ihm := ih (fun j tau hj hjm hget => hwin j tau hj (Nat.lt_succ_of_lt hjm) hget)
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
          rw [NamedNode.tick_cache_eq, phase_clip]
          refine clipResult_ne_none _ _ ?_
          unfold onPhaseTick
          set al := alignRound nd.cache (S.hc.round_of (S.E.slotOf t)) with hal
          have halign : cacheAtRound al r = cacheAtRound nd.cache r :=
            cacheAtRound_align nd.cache _ r hround hclock
          have hsome' : phaseResult (cacheAtRound al r) p ≠ none := by
            rw [halign]; exact ihm
          change phaseResult (cacheAtRound (clipCache nd.st.core.F
            ⟨al.round, completeFrame S.E S.hc nd.st.core.toHealing al.round t al.current,
              completeFrame S.E S.hc nd.st.core.toHealing (al.round + 1) t al.next⟩) r) p ≠ none
          rw [phase_clip]
          refine clipResult_ne_none _ _ ?_
          rw [phase_completed_cache S.E S.hc nd.st.core.toHealing al t r p hsome', halign]
          exact ihm
        · rw [Proofs.NamedRuntime.stateBefore_other S rho he v hvu]
          exact ihm
      | deliver u o t =>
        by_cases hvu : v = u
        · subst hvu
          rw [Proofs.NamedRuntime.stateBefore_deliver S rho he]
          rw [NamedNode.process_cache_eq, phase_clip]
          exact clipResult_ne_none _ _ ihm
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
private theorem time_lt_of_lt_beforeIdx (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (t : Time)
    {j : Nat} {e : NamedEvent V} (hj : j < beforeIdx rho t)
    (hget : rho.events[j]? = some e) : e.time < t := by
  have hm : e ∈ rho.events.filter (fun x => decide (x.time < t)) := by
    rw [strict_filter_eq_take rho hsorted t]
    exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj]; exact hget)
  simpa only [decide_eq_true_eq] using (List.mem_filter.mp hm).2

omit [DecidableEq V] [Fintype V] in
/-- Every event through `j` passes the strict filter, so the post-event index is
inside the strict read. Same-time events are counted too. -/
private theorem lt_beforeIdx_of_time_lt (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (cut : Time)
    {j : Nat} {e : NamedEvent V} (he : rho.events[j]? = some e)
    (ht : e.time < cut) : j + 1 ≤ beforeIdx rho cut := by
  show j + 1 ≤ (rho.events.filter (fun x => decide (x.time < cut))).length
  obtain ⟨hjLen, hjGet⟩ := List.getElem?_eq_some_iff.mp he
  have htake : (rho.events.take (j + 1)).filter (fun x => decide (x.time < cut)) =
      rho.events.take (j + 1) := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp only [decide_eq_true_eq]
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
    have hklt : k < j + 1 := by
      have hlen := (List.getElem?_eq_some_iff.mp hk).1
      rw [List.length_take] at hlen
      exact hlen.trans_le (Nat.min_le_left _ _)
    have hkRun : rho.events[k]? = some x := by
      simpa only [List.getElem?_take_of_lt hklt] using hk
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hklt) with hkj | rfl
    · obtain ⟨hkLen, hkGet⟩ := List.getElem?_eq_some_iff.mp hkRun
      have hkey := (List.pairwise_iff_getElem.mp hsorted) k j hkLen hjLen hkj
      rw [hkGet, hjGet] at hkey
      exact (time_le_of_key_le hkey).trans_lt ht
    · have hxe : x = e := Option.some.inj (hkRun.symm.trans he)
      simpa only [hxe] using ht
  have hsplit : rho.events.filter (fun x => decide (x.time < cut)) =
      (rho.events.take (j + 1)).filter (fun x => decide (x.time < cut)) ++
      (rho.events.drop (j + 1)).filter (fun x => decide (x.time < cut)) := by
    conv_lhs => rw [← List.take_append_drop (j + 1) rho.events]
    rw [List.filter_append]
  have hlength := congrArg List.length hsplit
  rw [htake, List.length_append, List.length_take,
    Nat.min_eq_left (Nat.succ_le_of_lt hjLen)] at hlength
  omega

/-! ## The completion statement -/

/-- The strict read's `readFrame` is its raw cache lookup: the node invariant
already clips the whole cache against the reader's own finalized root, so
`readFrame`'s extra clip is idempotent. -/
private theorem read_raw (S : Setup V) (rho : NamedRun V) (v : V) (r : Round)
    (p : Phase) (u : Time) :
    phaseResult (DecoupledConsensusModel.Protocol.readFrame
        (NamedRun.stateBeforeTime S rho u v).cache
        (NamedRun.stateBeforeTime S rho u v).st.core.toHealing r) p =
      phaseResult (cacheAtRound (NamedRun.stateBeforeTime S rho u v).cache r) p := by
  have hclipped := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho u v).2.2
  change phaseResult (clipFrame (NamedRun.stateBeforeTime S rho u v).st.core.F
    (cacheAtRound (NamedRun.stateBeforeTime S rho u v).cache r)) p = _
  rw [← cacheAtRound_clip, hclipped]

/-- **Forward frame completion, from the tick.** Given the domain tick of round
`r` phase `p` as an event of the run, every strict read strictly after that
domain and at or before the next round's opening sees the phase-`p` slot of
the round-`r` frame completed, with the value the tick computed from the store
it read, clipped against the reader's own finalized root at the later read.

No honesty, fault bound, delivery or horizon premise is used here: the tick
event is supplied. `frame_phase_completed` below produces it from the schedule. -/
theorem frame_phase_completed_of_tick_in_round (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (v : V) (r : Round) (hr : 0 < r) (p : Phase)
    (i : Nat) (he : rho.events[i]? = some (.tick v (domain S.E S.hc r p)))
    (t : Time) (ht : domain S.E S.hc r p < t) (hta : t ≤ opening S.E S.hc (r + 1)) :
    phaseResult (DecoupledConsensusModel.Protocol.readFrame
        (NamedRun.stateBeforeTime S rho t v).cache
        (NamedRun.stateBeforeTime S rho t v).st.core.toHealing r) p =
      some ((freezeRoot S.E
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) v).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) v).st.core.F S.hc.η_SG r
        (early S.E S.hc r p) (late S.E S.hc r p)).map
          (fun B => clipGrade B (NamedRun.stateBeforeTime S rho t v).st.core.F)) := by
  have hsorted := core.sorted
  have hnodup := core.nodup
  -- 1. the domain tick closes the slot.
  have hbase : phaseResult (cacheAtRound
      (NamedRun.stateBefore S rho (i + 1) v).cache r) p ≠ none := by
    rw [Proofs.NamedRuntime.stateBefore_tick S rho he]
    set nd := NamedRun.stateBefore S rho i v with hnd
    rw [NamedNode.tick_cache_eq, phase_clip]
    refine clipResult_ne_none _ _ ?_
    unfold onPhaseTick
    set al := alignRound nd.cache
      (S.hc.round_of (S.E.slotOf (domain S.E S.hc r p))) with hal
    have haddr : r = al.round ∨ r = al.round + 1 :=
      domain_addressable S hr p al (by rw [hal, alignRound_round]; unfold clockRound; rfl)
    change phaseResult (cacheAtRound (clipCache nd.st.core.F
      ⟨al.round,
        completeFrame S.E S.hc nd.st.core.toHealing al.round
          (domain S.E S.hc r p) al.current,
        completeFrame S.E S.hc nd.st.core.toHealing (al.round + 1)
          (domain S.E S.hc r p) al.next⟩) r) p ≠ none
    rw [phase_clip]
    refine clipResult_ne_none _ _ ?_
    exact phase_domain_cache S.E S.hc nd.st.core.toHealing al
      (domain S.E S.hc r p) r p rfl haddr
  -- 2. the slot survives to the strict read of `t`.
  have hidx : i + 1 ≤ beforeIdx rho t :=
    lt_beforeIdx_of_time_lt rho hsorted t he ht
  have hstrict : phaseResult (cacheAtRound
      (NamedRun.stateBeforeTime S rho t v).cache r) p ≠ none := by
    rw [stateBeforeTime_eq_idx S rho hsorted t]
    refine slot_some_index S rho hsorted v r p (i + 1) hbase _ hidx ?_
    intro j tau _ hjm hget
    have hlt : NamedEvent.time (NamedEvent.tick v tau) < t :=
      time_lt_of_lt_beforeIdx rho hsorted t hjm hget
    change tau < t at hlt
    exact clockRound_le_of_lt_opening S (lt_of_lt_of_le hlt hta)
  -- 3. read the value back through the backward provenance row.
  obtain ⟨res, hres⟩ := Option.ne_none_iff_exists'.mp hstrict
  rw [read_raw, hres]
  rcases NamedCacheProvenance.completed_phase_before_read S rho hsorted hnodup
      t v r p res hres with ⟨hzero, _⟩ | ⟨j, tau, _, _, htau, hvalue⟩
  · exact absurd hzero (Nat.pos_iff_ne_zero.mp hr)
  · subst htau
    rw [hvalue]


/-- **Forward frame completion (row Q22).** For an honest node and a positive
round whose phase-`p` domain is inside the run horizon, every strict read
strictly after that domain and at or before `a_r` returns the completed
phase-`p` result of the round-`r` frame, namely the freeze computed at the
domain tick from the store that tick read, clipped against the reader's own
finalized root.

`htick` is the one premise the admissible core does not carry: the domain tick
exists because `NamedScheduleWellFormed.tick_total` makes every honest node tick
at every public time inside `[0, horizon]`, and `domain r p` is public for
`0 < r` (it is `(4rR + k)Δ` with `k ∈ {1, 0, -1}`) and nonnegative, but nothing
in `NamedAdmissibleCore` bounds it by `rho.horizon`. The claim is false without
it: a run that open items before the domain never ticks there and the slot stays
pending. `RoundIncluded S rho b0 r` supplies it, through `domain_le_a`. -/
theorem frame_phase_completed_in_round (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (v : V) (hv : v ∈ rho.honest)
    (r : Round) (hr : 0 < r) (p : Phase) (t : Time)
    (ht : domain S.E S.hc r p < t) (hta : t ≤ opening S.E S.hc (r + 1))
    (htick : domain S.E S.hc r p ≤ rho.horizon) :
    phaseResult (DecoupledConsensusModel.Protocol.readFrame
        (NamedRun.stateBeforeTime S rho t v).cache
        (NamedRun.stateBeforeTime S rho t v).st.core.toHealing r) p =
      some ((freezeRoot S.E
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) v).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) v).st.core.F S.hc.η_SG r
        (early S.E S.hc r p) (late S.E S.hc r p)).map
          (fun B => clipGrade B (NamedRun.stateBeforeTime S rho t v).st.core.F)) := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp
    (core.tick_total v hv (domain S.E S.hc r p) (publicTime_domain S hr p)
      (domain_nonneg S hr p) htick)
  exact frame_phase_completed_of_tick_in_round S rho core v r hr p i hi t ht hta

/-- **Old form, as a corollary.** `a_r` is strictly inside round `r`
(`FrameForward.a_lt_opening_succ`), so the action-time bound is the special case
of the clock-round bound. -/
theorem frame_phase_completed (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (v : V) (hv : v ∈ rho.honest)
    (r : Round) (hr : 0 < r) (p : Phase) (t : Time)
    (ht : domain S.E S.hc r p < t) (hta : t ≤ S.a r)
    (htick : domain S.E S.hc r p ≤ rho.horizon) :
    phaseResult (DecoupledConsensusModel.Protocol.readFrame
        (NamedRun.stateBeforeTime S rho t v).cache
        (NamedRun.stateBeforeTime S rho t v).st.core.toHealing r) p =
      some ((freezeRoot S.E
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) v).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) v).st.core.F S.hc.η_SG r
        (early S.E S.hc r p) (late S.E S.hc r p)).map
          (fun B => clipGrade B (NamedRun.stateBeforeTime S rho t v).st.core.F)) :=
  frame_phase_completed_in_round S rho core v hv r hr p t ht
    (le_of_lt (lt_of_le_of_lt hta (FrameForward.a_lt_opening_succ S r))) htick



/-- The G2 slot form, in the field projection every caller uses. -/
theorem frame_g2_completed_in_round (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (v : V) (hv : v ∈ rho.honest)
    (r : Round) (hr : 0 < r) (t : Time)
    (ht : domain S.E S.hc r .g2 < t) (hta : t ≤ opening S.E S.hc (r + 1))
    (htick : domain S.E S.hc r .g2 ≤ rho.horizon) :
    (DecoupledConsensusModel.Protocol.readFrame
        (NamedRun.stateBeforeTime S rho t v).cache
        (NamedRun.stateBeforeTime S rho t v).st.core.toHealing r).g2 =
      some ((freezeRoot S.E
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.F S.hc.η_SG r
        (early S.E S.hc r .g2) (late S.E S.hc r .g2)).map
          (fun B => clipGrade B (NamedRun.stateBeforeTime S rho t v).st.core.F)) :=
  frame_phase_completed_in_round S rho core v hv r hr .g2 t ht hta htick

/-- **Old form, as a corollary.** -/
theorem frame_g2_completed (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (v : V) (hv : v ∈ rho.honest)
    (r : Round) (hr : 0 < r) (t : Time)
    (ht : domain S.E S.hc r .g2 < t) (hta : t ≤ S.a r)
    (htick : domain S.E S.hc r .g2 ≤ rho.horizon) :
    (DecoupledConsensusModel.Protocol.readFrame
        (NamedRun.stateBeforeTime S rho t v).cache
        (NamedRun.stateBeforeTime S rho t v).st.core.toHealing r).g2 =
      some ((freezeRoot S.E
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.F S.hc.η_SG r
        (early S.E S.hc r .g2) (late S.E S.hc r .g2)).map
          (fun B => clipGrade B (NamedRun.stateBeforeTime S rho t v).st.core.F)) :=
  frame_phase_completed S rho core v hv r hr .g2 t ht hta htick


#print axioms frame_phase_completed_of_tick_in_round
#print axioms frame_phase_completed_in_round
#print axioms frame_phase_completed
#print axioms frame_g2_completed_in_round
#print axioms frame_g2_completed

end DecoupledConsensusModel.Proofs.FrameCompleted

end
