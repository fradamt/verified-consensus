module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.Monotone

@[expose] public section

/-!
# P3(a) — the `t_GST = 0` view lemmas
(design §4.D; PROTOCOL.md#the-complete-protocol)

What synchrony gives the availability proof, and what it still owes.

**Broadcast, specialized.** `Synchrony.broadcast` is stated with `max t t_GST`
so that one clause covers both sides of GST. At `t_GST = 0` the `max`
collapses — every event of a run lies in `[0, horizon]`
(`ScheduleWellFormed.in_horizon`), so `t ≥ 0` — and the clause reads: *an
object one honest node emits at `t` is processed by every honest node strictly
before `t + Δ`*. That is `broadcast_gst_zero`, and it is the only place the
`max` has to be reasoned about.

**Stamps are at most processing times.** `Proofs/Execution.lean`'s
`stamp_is_last_tick` already says the clock a delivery is stamped with is the
receiver's last tick, which is at most the delivery time. So "processed before
`Γ`" gives "stamped before `Γ`" for free — the *easy* direction, and the one the
late cutoff needs.

**The converse holds too, and the tick grid is what gives it.** The early cutoff
needs *stamped before `t_s + 2Δ` implies processed before `t_s + 2Δ`*. An honest
node ticks at every public time (`tick_total`), the public times are the
multiples of `Δ` (`Props/Execution/Setup.lean`), so a delivery is never more than
`Δ` past the clock it reads: if it were, the tick at `p + Δ` would itself be an
earlier event of the prefix, contradicting the maximality of `Run.lastTickIn`.
Three steps, all proved here:

* `le_lastTickIn` — `Run.lastTickIn` is the *latest* tick along a time-sorted
  list, the counterpart of `Proofs/Execution.lean`'s `tick_mem_of_lastTickIn`;
* `mem_take_of_key_lt` — an earlier-keyed event lies inside the prefix a delivery
  reads, which is the same-instant rule of PROTOCOL.md#the-complete-protocol doing its
  work: a tick at `p ≤ t` has key `(p, 0)` and the delivery has key `(t, 1)`;
* `store_time_close` and `processed_lt_of_store_time_lt` — the grid bound and its
  cutoff form.

What `Main.lean`'s `EvaluationReaches` still covers is the rest of the chain, not
the timestamps: that an honest voter's head at `t_s + Δ` really is the honest
proposal, which is the §6 fork choice's own agreement argument.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Relay at `t_GST = 0` -/







/-! ## The tick grid: `Run.lastTickIn` is the latest tick -/

omit [Fintype V] in
/-- A list holding a tick of `v` has a recorded last tick of `v`. -/
theorem lastTickIn_isSome_of_mem (v : V) :
    ∀ (l : List (Event V)) (t : Time), Event.tick v t ∈ l →
      (Run.lastTickIn v l).isSome := by
  intro l
  induction l with
  | nil => intro t hmem; simp at hmem
  | cons e l ih =>
      intro t hmem
      simp only [Run.lastTickIn]
      cases hl : Run.lastTickIn v l with
      | some u => simp
      | none =>
          rcases List.mem_cons.mp hmem with hEq | hin
          · subst hEq
            simp
          · exact absurd (ih t hin) (by rw [hl]; simp)

omit [Fintype V] in
/-- **`Run.lastTickIn` is maximal along a time-sorted list.** Every tick of `v`
in the list is at or before the recorded one.

`Proofs/Execution.lean` proves the other half — that the recorded tick really
happened (`tick_mem_of_lastTickIn`) — and the two together say the store clock
a delivery reads is exactly the receiver's latest earlier tick. -/
theorem le_lastTickIn (v : V) :
    ∀ (l : List (Event V)), l.Pairwise (fun e f => e.time ≤ f.time) →
      ∀ (t t' : Time), Event.tick v t ∈ l → Run.lastTickIn v l = some t' → t ≤ t' := by
  intro l
  induction l with
  | nil => intro _ t t' hmem _; simp at hmem
  | cons e l ih =>
      intro hs t t' hmem hlast
      rw [List.pairwise_cons] at hs
      simp only [Run.lastTickIn] at hlast
      cases hl : Run.lastTickIn v l with
      | some u =>
          rw [hl] at hlast
          have hu : u = t' := by simpa using hlast
          subst hu
          rcases List.mem_cons.mp hmem with hEq | hin
          · have hle := hs.1 _ (tick_mem_of_lastTickIn v l hl)
            rw [← hEq] at hle
            exact hle
          · exact ih hs.2 t u hin hl
      | none =>
          rw [hl] at hlast
          rcases List.mem_cons.mp hmem with hEq | hin
          · subst hEq
            simp only [reduceIte, Option.some.injEq] at hlast
            exact le_of_eq hlast
          · exact absurd (lastTickIn_isSome_of_mem v l t hin) (by rw [hl]; simp)

/-! ## An earlier-keyed event lies in the prefix a delivery reads -/

/-- An event whose key is strictly below the `i`-th event's key is among the
first `i` events (PROTOCOL.md#the-complete-protocol).

This is the same-instant rule doing its work: a tick at a public time `p ≤ t` has
key `(p, 0)`, a delivery at `t` has key `(t, 1)`, and `(p, 0) < (t, 1)`, so the
tick is inside the prefix whose fold the delivery reads. Sortedness alone gives
it; `nodup` is not needed. -/
theorem mem_take_of_key_lt (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    {i : Nat} {e f : Event V} (hi : ρ.events[i]? = some f) (hmem : e ∈ ρ.events)
    (hlt : NamedEvent.key e < NamedEvent.key f) : e ∈ ρ.events.take i := by
  obtain ⟨hbound, hget⟩ := List.getElem?_eq_some_iff.mp hi
  have hsplit : ρ.events = ρ.events.take i ++ f :: ρ.events.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i ρ.events]
    rw [List.drop_eq_getElem_cons hbound, hget]
  have hpair : ρ.events.Pairwise (fun e f => NamedEvent.key e ≤ NamedEvent.key f) :=
    sch.sorted
  rw [hsplit] at hpair hmem
  rcases List.mem_append.mp hmem with h | h
  · exact h
  rcases List.mem_cons.mp h with h | h
  · exact absurd hlt (by rw [h]; exact lt_irrefl _)
  · have hkey : NamedEvent.key f ≤ NamedEvent.key e :=
      (List.pairwise_cons.mp (List.pairwise_append.mp hpair).2.1).1 e h
    exact absurd hlt (not_lt_of_ge hkey)

/-- The tick-before-delivery instance of `mem_take_of_key_lt`: a tick of `v` at
`p ≤ t` precedes a delivery at `t` in the event list. -/
theorem tick_mem_take (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    {i : Nat} {v w : V} {o : Object V} {t p : Time}
    (hi : ρ.events[i]? = some (Event.deliver w o t)) (hmem : Event.tick v p ∈ ρ.events)
    (hle : p ≤ t) : Event.tick v p ∈ ρ.events.take i := by
  refine mem_take_of_key_lt S sch hi hmem ?_
  rw [NamedEvent.key, NamedEvent.key, Prod.Lex.toLex_lt_toLex]
  rcases lt_or_eq_of_le hle with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, by simp [NamedEvent.phase]⟩

/-- **The clock a delivery reads is at least any earlier tick of the receiver.**
With `tick_total` — an honest node ticks at every public time — the caller reads
this as "the stamp is at least the greatest multiple of `Δ` at or below the
delivery time", which is the lower half of the tick-grid bound.

The upper half is `Proofs/Execution.lean`'s `stamp_is_last_tick`. -/
theorem tick_le_store_time (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    {i : Nat} {v : V} {o : Object V} {t p : Time}
    (hi : ρ.events[i]? = some (Event.deliver v o t)) (hmem : Event.tick v p ∈ ρ.events)
    (hle : p ≤ t) : p ≤ (ρ.stateBefore S i v).st.t := by
  have htake : Event.tick v p ∈ ρ.events.take i := tick_mem_take S sch hi hmem hle
  have hEq : (ρ.stateBefore S i v).st.t = (Run.lastTickIn v (ρ.events.take i)).getD 0 :=
    store_time_eq_lastTick S ρ v i
  rw [hEq]
  cases hl : Run.lastTickIn v (ρ.events.take i) with
  | none =>
      exfalso
      have hsome := lastTickIn_isSome_of_mem v _ p htake
      rw [hl] at hsome
      simp at hsome
  | some u =>
      simp only [Option.getD]
      exact le_lastTickIn v (ρ.events.take i)
        ((pairwise_time_le S sch).sublist (List.take_sublist i ρ.events)) p u htake hl

/-! ## The tick grid closes the gap between stamp and processing time -/

/-- **The clock a delivery reads is within `Δ` of the delivery time.**

An honest node ticks at *every* public time (`tick_total`) and the public times
are the multiples of `Δ` (`Props/Execution/Setup.lean`), so if the delivery at
`t` were at or after `p + Δ`, where `p` is the recorded last tick, then the tick
at `p + Δ` would itself be an earlier event of the prefix — contradicting
`le_lastTickIn`. This is the converse of `stamp_is_last_tick`'s bound and the
step the early-cutoff argument needs. -/
theorem store_time_close (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    {i : Nat} {v : V} {o : Object V} {t : Time} (hv : v ∈ ρ.honest)
    (hi : ρ.events[i]? = some (Event.deliver v o t)) :
    t < (ρ.stateBefore S i v).st.t + S.E.Δ := by
  have hdel : Event.deliver v o t ∈ ρ.events := List.mem_of_getElem? hi
  obtain ⟨ht0, hthor⟩ := sch.in_horizon _ hdel
  have htick0 : Event.tick v 0 ∈ ρ.events :=
    NamedScheduleWellFormed.tick_total sch v hv 0 ⟨0, by simp⟩ (le_refl 0)
      (le_trans ht0 hthor)
  have htake0 : Event.tick v 0 ∈ ρ.events.take i := tick_mem_take S sch hi htick0 ht0
  have hEq : (ρ.stateBefore S i v).st.t = (Run.lastTickIn v (ρ.events.take i)).getD 0 :=
    store_time_eq_lastTick S ρ v i
  rw [hEq]
  cases hl : Run.lastTickIn v (ρ.events.take i) with
  | none =>
      exfalso
      have hsome := lastTickIn_isSome_of_mem v _ 0 htake0
      rw [hl] at hsome
      simp at hsome
  | some p =>
      simp only [Option.getD]
      rcases lt_or_ge t (p + S.E.Δ) with hlt | hcon
      · exact hlt
      exfalso
      have hpmem : Event.tick v p ∈ ρ.events.take i := tick_mem_of_lastTickIn v _ hl
      have hpev : Event.tick v p ∈ ρ.events :=
        (List.take_sublist i ρ.events).mem hpmem
      obtain ⟨k, hk⟩ := NamedScheduleWellFormed.tick_public sch v p hpev
      have hp0 : 0 ≤ p := (sch.in_horizon _ hpev).1
      have hpub' : PublicTime S (p + S.E.Δ) :=
        ⟨k + 1, by rw [hk]; push_cast; ring⟩
      have hnn : (0 : Time) ≤ p + S.E.Δ := by
        have key : ∀ a d : Int, 0 ≤ a → 0 < d → 0 ≤ a + d := by intro a d h₁ h₂; omega
        exact key p S.E.Δ hp0 S.E.Δ_pos
      have htick : Event.tick v (p + S.E.Δ) ∈ ρ.events :=
        NamedScheduleWellFormed.tick_total sch v hv _ hpub' hnn (le_trans hcon hthor)
      have htk : Event.tick v (p + S.E.Δ) ∈ ρ.events.take i :=
        tick_mem_take S sch hi htick hcon
      have hmax := le_lastTickIn v (ρ.events.take i)
        ((pairwise_time_le S sch).sublist (List.take_sublist i ρ.events))
        (p + S.E.Δ) p htk hl
      have key : ∀ a d : Int, a + d ≤ a → 0 < d → False := by intro a d h₁ h₂; omega
      exact key p S.E.Δ hmax S.E.Δ_pos

/-- **Stamped before a public time implies processed before it.**

`update_confirmation`'s cutoffs are public times, so a vote whose stamp is
strictly below the support cutoff was *delivered* strictly below it: the stamp is
a tick time, both are multiples of `Δ`, and the delivery is within `Δ` of the
stamp (`store_time_close`).

This is the direction the early set needs, and with `stamp_is_last_tick` — the
other direction — it closes the timestamp half of `Main.lean`'s
`EvaluationReaches`. -/
theorem processed_lt_of_store_time_lt (S : Setup V) {ρ : Run V}
    (sch : ScheduleWellFormed S ρ) {i : Nat} {v : V} {o : Object V} {t Γ : Time}
    (hv : v ∈ ρ.honest) (hi : ρ.events[i]? = some (Event.deliver v o t))
    (hpub : PublicTime S Γ) (hstamp : (ρ.stateBefore S i v).st.t < Γ) : t < Γ := by
  have hclose := store_time_close S sch hv hi
  obtain ⟨m, hm⟩ := hpub
  have hEq : (ρ.stateBefore S i v).st.t = (Run.lastTickIn v (ρ.events.take i)).getD 0 :=
    store_time_eq_lastTick S ρ v i
  rw [hEq] at hclose hstamp
  cases hl : Run.lastTickIn v (ρ.events.take i) with
  | none =>
      rw [hl] at hclose hstamp
      simp only [Option.getD] at hclose hstamp
      have hΔΓ : S.E.Δ ≤ Γ := by
        rcases Nat.eq_zero_or_pos m with hm0 | hmpos
        · exfalso
          rw [hm, hm0] at hstamp
          simp at hstamp
        · have h1 : (1 : Int) ≤ (m : Int) := by exact_mod_cast hmpos
          rw [hm]
          calc S.E.Δ = 1 * S.E.Δ := by ring
            _ ≤ (m : Int) * S.E.Δ :=
                Int.mul_le_mul_of_nonneg_right h1 (le_of_lt S.E.Δ_pos)
      have key : ∀ a d g : Int, a < 0 + d → d ≤ g → a < g := by
        intro a d g h₁ h₂; omega
      exact key t S.E.Δ Γ hclose hΔΓ
  | some p =>
      rw [hl] at hclose hstamp
      simp only [Option.getD] at hclose hstamp
      have hpev : Event.tick v p ∈ ρ.events :=
        (List.take_sublist i ρ.events).mem (tick_mem_of_lastTickIn v _ hl)
      obtain ⟨k, hk⟩ := NamedScheduleWellFormed.tick_public sch v p hpev
      have hkm : (k : Int) < (m : Int) := by
        rcases lt_or_ge (k : Int) (m : Int) with h | h
        · exact h
        · exfalso
          rw [hk, hm] at hstamp
          exact absurd hstamp (not_lt_of_ge
            (Int.mul_le_mul_of_nonneg_right h (le_of_lt S.E.Δ_pos)))
      have hstep : p + S.E.Δ ≤ Γ := by
        have hk1 : (k : Int) + 1 ≤ (m : Int) := by omega
        rw [hk, hm]
        calc (k : Int) * S.E.Δ + S.E.Δ = ((k : Int) + 1) * S.E.Δ := by ring
          _ ≤ (m : Int) * S.E.Δ :=
              Int.mul_le_mul_of_nonneg_right hk1 (le_of_lt S.E.Δ_pos)
      exact lt_of_lt_of_le hclose hstep

end Protocol
end DecoupledConsensusModel

end
