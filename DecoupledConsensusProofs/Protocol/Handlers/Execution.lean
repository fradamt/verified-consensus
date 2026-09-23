module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.NamedExecutionQueries
public import DecoupledConsensusInternal.Execution.Assumptions
public import DecoupledConsensusProofs.Objects.AdmissibleCore

@[expose] public section

/-!
# Execution layer — the two checks the layer rests on
(§2.2, §3, §3.1, §10)

Two facts have to hold before anything is stated over the trace layer, and the
plan asks for both before any other proof.

**The layer tracks the model.** `on_tick_emit_agrees` says the store and record
components of the emitting tick are `Protocol.on_tick`'s, branch for branch. If
`on_tick` changes, this breaks loudly — the same tripwire device
`Healing/Schedule.lean` uses for its seven alignments.

**Row C1 is a lemma, not an axiom.** `Σ.t` is written by ticks alone:
`on_block_checked`, `on_goldfish_vote` and `on_sg_vote` all stamp with
`Σ.t` and none of them writes it. So the clock a node's store holds at any prefix
is the time of that node's last tick, and an object delivered between two public
times carries the earlier one's stamp — because that is the last value written.
`store_time_eq_lastTick` is that fact and `stamp_is_last_tick` is its delivery
form. Adding a clock event would destroy the derivation (design §7).

`publicTime_iff` is the third check: the tick schedule of `Setup.lean` is exactly
the four per-slot instants of PROTOCOL.md#the-complete-protocol, which is what makes the view
freeze `t_s + 3Δ` a tick time (flag F-a).
-/

namespace DecoupledConsensusModel
namespace Execution

open Protocol (ChainState HeightConfig)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The tripwire (design §2.2) -/



/-! ## The tick schedule (design §3.1) -/

/-- The public times are exactly the four per-slot instants of
PROTOCOL.md#the-complete-protocol.

`t_s = 4Δs` and the instants are `t_s + kΔ` for `k ∈ {0,1,2,3}`, so every natural
multiple of `Δ` is one of them and conversely. Flag F-a follows: the view freeze
`t_s + 3Δ` is a tick time, even though no `on_tick` branch fires there. -/
theorem publicTime_iff (S : Setup V) (t : Time) :
    PublicTime S t ↔
      ∃ s : Slot, t = Protocol.proposal_time S.E s ∨ t = Protocol.vote_time S.E s ∨
        t = Protocol.support_cutoff S.E s ∨ t = Protocol.view_freeze S.E s := by
  unfold PublicTime Protocol.proposal_time Protocol.vote_time Protocol.support_cutoff
    Protocol.view_freeze Env.t slotStart
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨k / 4, ?_⟩
    have hk : (k : Time) = 4 * ((k / 4 : Nat) : Time) + ((k % 4 : Nat) : Time) := by
      have h : 4 * (k / 4) + k % 4 = k := Nat.div_add_mod k 4
      exact_mod_cast h.symm
    have h4 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
    rcases h4 with h | h | h | h
    · exact Or.inl (by rw [hk, h]; push_cast; ring)
    · exact Or.inr (Or.inl (by rw [hk, h]; push_cast; ring))
    · exact Or.inr (Or.inr (Or.inl (by rw [hk, h]; push_cast; ring)))
    · exact Or.inr (Or.inr (Or.inr (by rw [hk, h]; push_cast; ring)))
  · rintro ⟨s, h | h | h | h⟩
    · exact ⟨4 * s, by rw [h]; push_cast; ring⟩
    · exact ⟨4 * s + 1, by rw [h]; push_cast; ring⟩
    · exact ⟨4 * s + 2, by rw [h]; push_cast; ring⟩
    · exact ⟨4 * s + 3, by rw [h]; push_cast; ring⟩

/-! ## Row C1: `Σ.t` is written by ticks alone (design §3)

Seven handler lemmas, then the fold. Each handler either returns its input or
returns a record update that does not name `t`, so every one of them closes by
case split and `rfl` — which is exactly the content of "`Σ.t` is written by
`on_tick` alone". -/

omit [Fintype V] in
/-- §5.2 `update_finality` does not write `Σ.t` (PROTOCOL.md#the-complete-protocol). -/
theorem update_finality_time (st : Protocol.Store V) (σ : ChainState V) :
    (Protocol.update_finality st σ).t = st.t := by
  simp only [Protocol.update_finality]
  split_ifs <;> rfl

omit [Fintype V] in
/-- §7.2 `on_goldfish_vote` stamps with `Σ.t` and does not write it
(PROTOCOL.md#the-complete-protocol). -/
theorem on_goldfish_vote_time (st : Protocol.Store V) (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote st u).t = st.t := by
  simp only [Protocol.on_goldfish_vote]
  split_ifs <;> rfl

/-- The checked runtime guard also preserves `Σ.t`; its admitted branch is
the unchecked core handler above. -/
theorem on_goldfish_vote_checked_time (E : Env V) (st : Protocol.Store V)
    (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote_checked E st u).t = st.t := by
  simp only [Protocol.on_goldfish_vote_checked]
  split_ifs
  · exact on_goldfish_vote_time st u
  · rfl


/-- Unpacking carried votes through the checked runtime handler does not write
`Σ.t`. -/
theorem foldl_on_goldfish_vote_checked_time (E : Env V)
    (l : List (GoldfishVote V)) (st : Protocol.Store V) :
    (l.foldl (Protocol.on_goldfish_vote_checked E) st).t = st.t := by
  induction l generalizing st with
  | nil => rfl
  | cons u l ih =>
      rw [List.foldl_cons, ih, on_goldfish_vote_checked_time]



omit [Fintype V] in
/-- §7.2 `on_sg_vote` does not write `Σ.t` (PROTOCOL.md#the-complete-protocol). -/
theorem on_sg_vote_time (hc : Protocol.HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) : (Protocol.on_sg_vote hc st a).t = st.t := by
  simp only [Protocol.on_sg_vote]
  split_ifs <;> rfl

omit [Fintype V] in
/-- §5.2 `update_finality` does not write `Σ.s`. -/
theorem update_finality_slot (st : Protocol.Store V) (σ : ChainState V) :
    (Protocol.update_finality st σ).s = st.s := by
  simp only [Protocol.update_finality]
  split_ifs <;> rfl

omit [Fintype V] in
/-- §7.2 `on_goldfish_vote` does not write `Σ.s`. -/
theorem on_goldfish_vote_slot (st : Protocol.Store V) (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote st u).s = st.s := by
  simp only [Protocol.on_goldfish_vote]
  split_ifs <;> rfl

/-- The checked runtime guard also preserves `Σ.s`. -/
theorem on_goldfish_vote_checked_slot (E : Env V) (st : Protocol.Store V)
    (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote_checked E st u).s = st.s := by
  simp only [Protocol.on_goldfish_vote_checked]
  split_ifs
  · exact on_goldfish_vote_slot st u
  · rfl

/-- Unpacking carried votes through the checked runtime handler does not write
`Σ.s`. -/
theorem foldl_on_goldfish_vote_checked_slot (E : Env V)
    (l : List (GoldfishVote V)) (st : Protocol.Store V) :
    (l.foldl (Protocol.on_goldfish_vote_checked E) st).s = st.s := by
  induction l generalizing st with
  | nil => rfl
  | cons u l ih =>
      rw [List.foldl_cons, ih, on_goldfish_vote_checked_slot]

omit [Fintype V] in
/-- §7.2 `on_sg_vote` does not write `Σ.s`. -/
theorem on_sg_vote_slot (hc : Protocol.HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) : (Protocol.on_sg_vote hc st a).s = st.s := by
  simp only [Protocol.on_sg_vote]
  split_ifs <;> rfl

/-! ### The shared block body

The named path calls the shared `on_block_using` body with the named finality
transition, so the clock facts are needed for an arbitrary state builder. The
builder writes only the stored chain state, which is not `t` or `s`. -/

/-- The shared block body does not write `Σ.t`, whatever state it builds. -/
theorem on_block_using_time (E : Env V) (st : Protocol.Store V) (B : Block V)
    (build : ChainState V → ChainState V) :
    (Protocol.on_block_using E st B build).t = st.t := by
  simp only [Protocol.on_block_using]
  split_ifs <;>
    first
      | rfl
      | rw [update_finality_time, foldl_on_goldfish_vote_checked_time E]

/-- The shared block body does not write `Σ.s`, whatever state it builds. -/
theorem on_block_using_slot (E : Env V) (st : Protocol.Store V) (B : Block V)
    (build : ChainState V → ChainState V) :
    (Protocol.on_block_using E st B build).s = st.s := by
  simp only [Protocol.on_block_using]
  split_ifs <;>
    first
      | rfl
      | rw [update_finality_slot, foldl_on_goldfish_vote_checked_slot E]

/-! ### The named store steps

Every named wrapper reaches the erased core through one of the handlers above.
The retained named body and row fields are not the clock, so each wrapper's
clock fact is the corresponding core fact. -/

omit [Fintype V] in
/-- The named body commit keeps the core the shared handler produced. -/
theorem commitBlock_core (before : Protocol.NamedStore V) (after : Protocol.Store V)
    (B : NamedBlock V) : (Protocol.NamedStore.commitBlock before after B).core = after := by
  unfold Protocol.NamedStore.commitBlock
  split_ifs <;> rfl

omit [Fintype V] in
/-- Named row admission is the existing SG handler on the core. -/
theorem admit_row_core (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (a : NamedAttestation V) :
    (Protocol.NamedAdmission.admit_row hc st a).core =
      Protocol.on_sg_vote hc st.core a.erase := by
  dsimp only [Protocol.NamedAdmission.admit_row]
  split_ifs <;> rfl

omit [Fintype V] in
/-- Named row admission writes neither clock component. -/
theorem admit_row_clock (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (a : NamedAttestation V) :
    (Protocol.NamedAdmission.admit_row hc st a).core.t = st.core.t ∧
      (Protocol.NamedAdmission.admit_row hc st a).core.s = st.core.s := by
  rw [admit_row_core]
  exact ⟨on_sg_vote_time hc st.core a.erase, on_sg_vote_slot hc st.core a.erase⟩

omit [Fintype V] in
/-- The carried named row fold writes neither clock component. -/
theorem admit_rows_clock (hc : Protocol.HealConfig) :
    ∀ (rows : List (NamedAttestation V)) (st : Protocol.NamedStore V),
      (Protocol.NamedAdmission.admit_rows hc st rows).core.t = st.core.t ∧
        (Protocol.NamedAdmission.admit_rows hc st rows).core.s = st.core.s
  | [], _ => ⟨rfl, rfl⟩
  | a :: rows, st => by
      have h1 := admit_row_clock hc st a
      have h2 := admit_rows_clock hc rows (Protocol.NamedAdmission.admit_row hc st a)
      exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

/-- The named block core writes neither clock component. -/
theorem process_block_core_clock (E : Env V) (hc : Protocol.HealConfig)
    (cfg : HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedStore.process_block_core E hc cfg st B).core.t = st.core.t ∧
      (Protocol.NamedStore.process_block_core E hc cfg st B).core.s = st.core.s := by
  dsimp only [Protocol.NamedStore.process_block_core]
  split_ifs with hp
  · rw [commitBlock_core]
    dsimp only [Protocol.on_block_checked_using]
    split_ifs
    · exact ⟨on_block_using_time E st.core B.erase _, on_block_using_slot E st.core B.erase _⟩
    · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- Named block admission, core then carried rows, writes neither component. -/
theorem on_block_with_clock (adm : Protocol.CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : HeightConfig) (st : Protocol.NamedStore V)
    (B : NamedBlock V) :
    (Protocol.NamedAdmission.on_block_with adm E hc cfg st B).core.t = st.core.t ∧
      (Protocol.NamedAdmission.on_block_with adm E hc cfg st B).core.s = st.core.s := by
  have hb := process_block_core_clock E hc cfg st B
  cases adm with
  | alsoCarried =>
      dsimp only [Protocol.NamedAdmission.on_block_with, Protocol.NamedAdmission.admit_carried]
      split_ifs
      · have h := admit_rows_clock hc B.attestations
          (Protocol.NamedStore.process_block_core E hc cfg st B)
        exact ⟨h.1.trans hb.1, h.2.trans hb.2⟩
      · exact hb

/-! ### The four named duties -/

/-- The named proposal duty writes neither clock component. -/
theorem named_propose_clock (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st).1.core.t = st.core.t ∧
      (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st).1.core.s = st.core.s := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact ⟨rfl, rfl⟩
  · exact on_block_with_clock .alsoCarried E hc cfg st _

/-- The named Goldfish vote duty writes neither clock component. -/
theorem named_vote_clock (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st).1.core.t = st.core.t ∧
      (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st).1.core.s = st.core.s := by
  dsimp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split_ifs
  · exact ⟨on_goldfish_vote_checked_time E st.core _, on_goldfish_vote_checked_slot E st.core _⟩
  · exact ⟨rfl, rfl⟩

/-- The named confirmation duty writes only the two confirmation fields. -/
theorem named_confirmation_clock (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) (s : Slot) :
    (Protocol.NamedDuties.update_confirmation_with gc E hc st s).core.t = st.core.t ∧
      (Protocol.NamedDuties.update_confirmation_with gc E hc st s).core.s = st.core.s :=
  ⟨rfl, rfl⟩

/-- The named attestation duty's only store write is named row admission. -/
theorem named_attest_clock (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) :
    (Protocol.NamedDuties.attest_with gc E hc nd st record).1.core.t = st.core.t ∧
      (Protocol.NamedDuties.attest_with gc E hc nd st record).1.core.s = st.core.s :=
  admit_row_clock hc st _

/-- Any store property the four named duties preserve, and that the clock
staging establishes, holds of the tick's returned store. -/
theorem named_tick_preserves (P : Protocol.NamedStore V → Prop)
    (gc : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : HeightConfig) (nd : Protocol.Node V)
    (hp : ∀ st, P st → P (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st).1)
    (hv : ∀ st, P st → P (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st).1)
    (hcf : ∀ st s, P st → P (Protocol.NamedDuties.update_confirmation_with gc E hc st s))
    (ha : ∀ st record, P st → P (Protocol.NamedDuties.attest_with gc E hc nd st record).1)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time)
    (h : P (Protocol.NamedStore.setClock E st t)) :
    P (Protocol.NamedTick.tick gc E hc cfg nd st record t).1 := by
  dsimp only [Protocol.NamedTick.tick, Protocol.TickScheduler.runWith,
    Protocol.NamedTick.namedOps]
  split_ifs <;> solve_by_elim (maxDepth := 8) [hp, hv, hcf, ha, h]

/-- The named tick stamps both clock components from its own time argument. -/
theorem named_tick_clock (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time) :
    (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.core.t = t ∧
      (Protocol.NamedTick.tick gc E hc cfg nd st record t).1.core.s = E.slotOf t := by
  refine named_tick_preserves
    (fun st' => st'.core.t = t ∧ st'.core.s = E.slotOf t) gc E hc cfg nd ?_ ?_ ?_ ?_ st record t
    ⟨rfl, rfl⟩
  · intro st' h
    exact ⟨(named_propose_clock gc E hc cfg nd st').1.trans h.1,
      (named_propose_clock gc E hc cfg nd st').2.trans h.2⟩
  · intro st' h
    exact ⟨(named_vote_clock gc E hc nd st').1.trans h.1,
      (named_vote_clock gc E hc nd st').2.trans h.2⟩
  · intro st' s h
    exact ⟨(named_confirmation_clock gc E hc st' s).1.trans h.1,
      (named_confirmation_clock gc E hc st' s).2.trans h.2⟩
  · intro st' record' h
    exact ⟨(named_attest_clock gc E hc nd st' record').1.trans h.1,
      (named_attest_clock gc E hc nd st' record').2.trans h.2⟩

/-! ### The named execution steps -/

/-- **Row C1's tick form.** The named tick stamps the store clock and the store
slot from the tick's own time; the phase cache and the retained signing record
are not the store. -/
theorem on_tick_emit_time (S : Setup V) : Execution.NamedTickTimeQuery S := by
  intro v before t
  exact named_tick_clock _ S.E S.hc S.cfg (S.node v) before.st before.record t

/-- Processing an object leaves both clock components: the three named handlers
reach the core through `on_block_using`, `on_goldfish_vote_checked` and
`on_sg_vote`, and all three stamp with `Σ.t` rather than writing it. -/
theorem process_time (S : Setup V) : Execution.NamedProcessTimeQuery S := by
  intro n o
  cases o with
  | block B => exact on_block_with_clock .alsoCarried S.E S.hc S.cfg n.st B
  | gfVote u =>
      exact ⟨on_goldfish_vote_checked_time S.E n.st.core u,
        on_goldfish_vote_checked_slot S.E n.st.core u⟩
  | attest a => exact admit_row_clock S.hc n.st a

/-- **Row C1, fold form.** After any event list, a node's `Σ.t` is the time of
its last tick in that list, or the clock it started with. Only the node's own
tick writes the field, and deliveries to other nodes leave its state alone. -/
theorem foldl_step_time (S : Setup V) : Execution.NamedFoldStepTimeQuery S := by
  intro w l v
  induction l generalizing w with
  | nil => rfl
  | cons e l ih =>
      rw [List.foldl_cons, ih]
      cases hl : Run.lastTickIn v l with
      | some t' => simp [Run.lastTickIn, hl]
      | none =>
          simp only [Run.lastTickIn, hl, Option.getD]
          cases e with
          | tick u t' =>
              by_cases hu : u = v
              · subst hu
                simp only [Execution.NamedWorld.step, Function.update_self]
                exact (on_tick_emit_time S u (w u) t').1
              · simp only [Execution.NamedWorld.step,
                  Function.update_of_ne (Ne.symm hu), if_neg hu]
          | deliver u o t' =>
              by_cases hu : u = v
              · subst hu
                simp only [Execution.NamedWorld.step, Function.update_self]
                exact (process_time S (w u) o).1
              · simp only [Execution.NamedWorld.step, Function.update_of_ne (Ne.symm hu)]

/-- **Row C1 at a run prefix.** The clock `v`'s store holds after `i` events is
the time of `v`'s last tick among them; the initial store's clock is zero, so a
node that has not ticked reads zero. -/
theorem store_time_eq_lastTick (S : Setup V) (rho : Execution.NamedRun V) :
    Execution.NamedStoreTimeEqLastTickQuery S rho := by
  intro v i
  have h := foldl_step_time S (Execution.NamedWorld.init : Execution.NamedWorld V)
    (rho.events.take i) v
  rw [show ((Execution.NamedWorld.init : Execution.NamedWorld V) v).st.core.t
      = (0 : Time) from rfl] at h
  exact h

omit [Fintype V] in
/-- A recorded last tick really happened. -/
theorem tick_mem_of_lastTickIn (v : V) :
    ∀ (l : List (Event V)) {t : Time}, Run.lastTickIn v l = some t → Event.tick v t ∈ l
  | [], _, h => by simp [Run.lastTickIn] at h
  | e :: l, t, h => by
      simp only [Run.lastTickIn] at h
      cases hl : Run.lastTickIn v l with
      | some t' =>
          rw [hl] at h
          have ht : t' = t := by simpa using h
          subst ht
          exact List.mem_cons_of_mem _ (tick_mem_of_lastTickIn v l hl)
      | none =>
          rw [hl] at h
          cases e with
          | tick u t'' =>
              by_cases hu : u = v
              · subst hu
                have ht : t'' = t := by simpa using h
                subst ht
                exact List.mem_cons_self ..
              · simp [hu] at h
          | deliver u o t'' => simp at h

/-- Sortedness, at one index: every event of a prefix is at most as late as the
event that follows it (PROTOCOL.md#the-complete-protocol). -/
theorem time_le_of_mem_take (S : Setup V) {ρ : Run V} (sch : ScheduleWellFormed S ρ)
    {i : Nat} {f : Event V} (hf : ρ.events[i]? = some f) :
    ∀ e ∈ ρ.events.take i, e.time ≤ f.time := by
  intro e he
  obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp hf
  have hsplit : ρ.events = ρ.events.take i ++ f :: ρ.events.drop (i + 1) := by
    conv_lhs => rw [← List.take_append_drop i ρ.events]
    rw [List.drop_eq_getElem_cons hi, hget]
  have hpair := sch.sorted
  change List.Pairwise (fun e f : Event V => Event.key e ≤ Event.key f) ρ.events at hpair
  rw [hsplit] at hpair
  have hkey : Event.key e ≤ Event.key f :=
    (List.pairwise_append.mp hpair).2.2 e he f (List.mem_cons_self ..)
  rcases Prod.Lex.le_iff.mp hkey with h | ⟨h, _⟩
  · exact le_of_lt h
  · exact le_of_eq h


end Execution
end DecoupledConsensusModel

end
