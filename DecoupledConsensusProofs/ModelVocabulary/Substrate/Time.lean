module
public import DecoupledConsensusModel.Objects.Time
public import Mathlib.Order.WithBot
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Data.Finset.Basic
public import DecoupledConsensusModel.Objects.Identifiers

@[expose] public section

/-!
# §1 Time, timestamps and strict cutoff views

The time domain is `Int` (modeling-choices row 9): the document needs only
`4Δs` arithmetic and strict comparisons, and `Γ_r^{−1} = t_0 − Δ` is negative at
round 0 (F1.3).

Two infinities appear. `Σ.timestamp(B_gen) = −∞` (PROTOCOL.md `def:store`,
`sec:complete-store`), so a
stamp is a `WithBot Time`; the §6 batch summary uses `t_v = e_v = +∞` for "never
occurred", so an occurrence is a `WithTop Time`.

`Σ.timestamp[·]` is written exactly once, when the object first enters its pool,
and never changes (PROTOCOL.md `sec:substrate`, `sec:goldfish-store`). A
rejected object is never
stamped at all (modeling-choices rows 4 and 10), so the map is partial. Every
phase cutoff is then a **strict** inequality over frozen stamps, which is what
makes `beforeCutoff` immutable.

A cutoff reads one of **two** clocks, and the τ fold is what split them
(PROTOCOL.md `sec:goldfish-store`, "resolution time"). The receipt clock is
`Σ.timestamp[·]` itself, read
through `stampedBefore` / `beforeCutoff`. The resolution clock is
`τ(x) = max{Σ.timestamp(x), Σ.timestamp(H)}` for an object naming a block `H`,
infinite while `H` is missing; it is read through `resolvedBefore` /
`beforeResolution`. Neither clock mutates: `τ` is a maximum of two frozen
stamps, not a re-stamping.
-/



namespace DecoupledConsensusModel

variable {α : Type}

/-- §1 the two cutoff tests are one test (PROTOCOL.md `sec:substrate`). -/
theorem stampedBefore_eq_occurrenceBefore (ts : TimestampMap α) (Γ : Time) (x : α) :
    stampedBefore ts Γ x = occurrenceBefore (ts x) Γ := rfl

/-- §6 `e_v ≥ Γ`, the negation of the cutoff test (PROTOCOL.md `alg:grades`).
`+∞` satisfies it, which is the "no equivocating vote exists" case. -/
def occurrenceAtLeast (x : Occurrence) (Γ : Time) : Bool :=
  !occurrenceBefore x Γ

/-- §1 a wider cutoff sees more, at one occurrence (PROTOCOL.md `sec:substrate`). -/
theorem occurrenceBefore_mono {x : Occurrence} {Γ Γ' : Time} (h : Γ ≤ Γ')
    (hx : occurrenceBefore x Γ = true) : occurrenceBefore x Γ' = true := by
  cases hs : x with
  | none => rw [hs] at hx; exact absurd hx (by simp [occurrenceBefore])
  | some u =>
    rw [hs] at hx
    simp only [occurrenceBefore, decide_eq_true_eq] at hx ⊢
    exact lt_of_lt_of_le hx (by exact_mod_cast h)

theorem occurrenceAtLeast_anti {x : Occurrence} {Γ Γ' : Time} (h : Γ' ≤ Γ)
    (hx : occurrenceAtLeast x Γ = true) : occurrenceAtLeast x Γ' = true := by
  simp only [occurrenceAtLeast, Bool.not_eq_true'] at hx ⊢
  by_contra hno
  rw [Bool.not_eq_false] at hno
  exact absurd (occurrenceBefore_mono h hno) (by rw [hx]; simp)

/-- §2 a `τ` bound is a bound on each side (PROTOCOL.md `sec:goldfish-store`,
"resolution time"). -/
theorem occurrenceBefore_of_max_left {x y : Occurrence} {Γ : Time}
    (h : occurrenceBefore (occurrenceMax x y) Γ = true) :
    occurrenceBefore x Γ = true := by
  cases hx : x with
  | none => rw [hx] at h; exact absurd h (by simp [occurrenceMax, occurrenceBefore])
  | some a =>
    cases hy : y with
    | none => rw [hx, hy] at h; exact absurd h (by simp [occurrenceMax, occurrenceBefore])
    | some b =>
      rw [hx, hy] at h
      simp only [occurrenceMax, occurrenceBefore, decide_eq_true_eq] at h ⊢
      exact lt_of_le_of_lt (le_max_left a b) h

/-- §2 the maximum is bounded when both sides are (PROTOCOL.md `sec:goldfish-store`,
"resolution time"). -/
theorem occurrenceBefore_max {x y : Occurrence} {Γ : Time}
    (hx : occurrenceBefore x Γ = true) (hy : occurrenceBefore y Γ = true) :
    occurrenceBefore (occurrenceMax x y) Γ = true := by
  cases hxe : x with
  | none => rw [hxe] at hx; exact absurd hx (by simp [occurrenceBefore])
  | some a =>
    cases hye : y with
    | none => rw [hye] at hy; exact absurd hy (by simp [occurrenceBefore])
    | some b =>
      rw [hxe] at hx; rw [hye] at hy
      simp only [occurrenceMax, occurrenceBefore, decide_eq_true_eq] at hx hy ⊢
      exact max_lt hx hy

end DecoupledConsensusModel

end
